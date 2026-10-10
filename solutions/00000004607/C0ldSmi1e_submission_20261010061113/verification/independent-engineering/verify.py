#!/usr/bin/env python3
"""Independent offline Lean review, using cached stock imports (not a Mathlib rebuild).

prepare STOCK LEAN_BIN OUT
verify SUBMISSION FROZEN_JSON STOCK LEAN_BIN OUT

FROZEN_JSON accepts a plain path->SHA256 map, the author's files-array manifest,
or {"frozen": true, "files": {"relative/path": "sha256", ...},
    "capstones": ["Optional.exact.declaration", ...]}.
Passing the manifest explicitly selects its current bytes for the frozen run.
Every fresh output directory is retained on failure. The input proof, runtime,
and stock trees are read only. Requires macOS cp -cR for private cache clones.
"""
import hashlib, json, os, pathlib, re, shutil, subprocess, sys, time

P = pathlib.Path
PERMITTED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|unsafe|partial|native_decide|implemented_by|extern)\b|Lean\.ofReduceBool|set_option\s+(debug\.skipKernelTC|trustLevel)")
RESERVED = {"Verification", "ReviewControls"}


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1048576), b""):
            h.update(chunk)
    return h.hexdigest()


def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


def code_only(text):
    """Erase nested Lean comments and strings, retaining line numbers for a token scan."""
    output, i, depth, string = [], 0, 0, False
    while i < len(text):
        c, pair = text[i], text[i:i+2]
        if depth:
            if pair == "/-": depth += 1; output.append("  "); i += 2
            elif pair == "-/": depth -= 1; output.append("  "); i += 2
            else: output.append("\n" if c == "\n" else " "); i += 1
        elif string:
            if c == "\\" and i+1 < len(text): output.append("  "); i += 2
            else:
                output.append("\n" if c == "\n" else " "); i += 1
                if c == '"': string = False
        elif pair == "/-": depth = 1; output.append("  "); i += 2
        elif pair == "--":
            j = text.find("\n", i)
            if j < 0: j = len(text)
            output.append(" " * (j-i)); i = j
        elif c == '"': string = True; output.append(" "); i += 1
        else: output.append(c); i += 1
    assert depth == 0 and not string, "Unterminated comment/string in active source"
    return "".join(output)


class Review:
    def __init__(self, stock, leanbin, out):
        self.stock, self.leanbin, self.out = map(lambda p: P(p).absolute(), (stock, leanbin, out))
        self.out.mkdir(parents=True, exist_ok=False)
        shutil.copy2(P(__file__), self.out / "driver.py.txt")
        self.project = self.out / "project"; self.project.mkdir()
        self.receipts = self.out / "receipts"; self.receipts.mkdir()
        self.env = os.environ.copy()
        for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LAKE_HOME", "LEAN_SYSROOT"):
            self.env.pop(key, None)
        self.env["PATH"] = str(self.leanbin) + ":" + self.env.get("PATH", "")
        self.env["GIT_OPTIONAL_LOCKS"] = "0"
        self.counter = 0
        self.module_paths = [self.stock / ".lake/build/lib/lean"]
        self.module_paths += [p / ".lake/build/lib/lean" for p in sorted((self.stock / ".lake/packages").iterdir()) if p.is_dir()]
        self.lib = self.project / ".lake/build/lib/lean"
        self.lib.mkdir(parents=True)
        self.env["LEAN_PATH"] = ":".join(map(str, [self.lib, *self.module_paths]))

    def run(self, argv, expected=0, cwd=None):
        self.counter += 1
        prefix = self.receipts / f"{self.counter:04d}"
        cwd = cwd or self.project
        start = time.time()
        actual = list(map(str,argv))
        result = subprocess.run(actual, cwd=cwd, env=self.env, capture_output=True)
        prefix.with_suffix(".stdout").write_bytes(result.stdout)
        prefix.with_suffix(".stderr").write_bytes(result.stderr)
        save(prefix.with_suffix(".json"), {
            "argv": list(map(str, argv)), "effective_argv":actual, "cwd": str(cwd), "exit_code": result.returncode,
            "expected_exit": expected, "seconds": time.time()-start,
            "stdout_sha256": sha(prefix.with_suffix(".stdout")),
            "stderr_sha256": sha(prefix.with_suffix(".stderr")),
            "environment": {k:self.env[k] for k in ("PATH", "LEAN_PATH", "GIT_OPTIONAL_LOCKS") if k in self.env},
            "active_source_hashes": {str(p.relative_to(self.project)):sha(p) for p in self.project.rglob("*.lean") if ".lake" not in p.relative_to(self.project).parts}})
        print(f"{self.counter:04d}: exit {result.returncode}: {argv[-1]}", flush=True)
        if (expected == 0 and result.returncode != 0) or (expected == "nonzero" and result.returncode == 0):
            raise RuntimeError(f"Unexpected command result; preserved in {prefix}.stdout/.stderr")
        return result.stdout.decode(errors="replace")

    def compile(self, relative, strict=True, expected=0, output=True):
        dest = self.lib / P(relative).with_suffix(".olean")
        dest.parent.mkdir(parents=True, exist_ok=True)
        argv = [self.leanbin / "lean"]
        if strict: argv += ["-DwarningAsError=true"]
        if output: argv += ["-o", dest]
        return self.run([*argv, relative], expected=expected)

    def inspector(self):
        target = self.project / "Verification/ClosureAudit.lean"
        target.parent.mkdir()
        shutil.copy2(P(__file__).parent / "templates/ClosureAudit.lean.txt", target)
        self.compile("Verification/ClosureAudit.lean")

    def audit(self, modules, output, strict=True, kernel=True, expected=0):
        command = "audit_kernel_modules" if kernel else "audit_modules"
        if not strict: command = "inspect_modules"
        source = "".join("import " + m + "\n" for m in modules)
        source += "import Verification.ClosureAudit\n"
        source += f'#{command} [{", ".join(modules)}] "{output}"\n'
        path = self.project / ("Inspect" + str(self.counter) + ".lean")
        path.write_text(source)
        self.compile(path.name, expected=expected, output=False)
        data = json.loads((self.project / output).read_text())
        shutil.copy2(self.project / output, self.out / output)
        return data

    def controls(self):
        # New operational fixtures: no mathematics or controls from any old problem.
        fixtures = {
            "Good": "import Lean\nnamespace FreshFixture\ndef unchanged (n : Nat) : Nat := n\ntheorem unchanged_ok (n : Nat) : unchanged n = n := rfl\nend FreshFixture\n",
            "Axiom": "import Lean\nnamespace UnrelatedNamespace\naxiom unseen : False\nend UnrelatedNamespace\ntheorem harmless : True := True.intro\n",
            "Transitive": "import Lean\naxiom opaqueAssumption : False\nopaque intermediate : False := opaqueAssumption\ntheorem indirect : False := intermediate\n",
            "Sorry": "import Lean\ntheorem unfinished : False := by sorry\n",
            "Native": "import Lean\ntheorem generatedNative : (17 : Nat) + 5 = 22 := by native_decide\n",
            "Unsafe": "import Lean\nunsafe def runtimeOnly (n : Nat) : Nat := n\n"}
        directory = self.project / "ReviewControls"; directory.mkdir()
        results = []
        for name, source in fixtures.items():
            path = directory / (name + ".lean"); path.write_text(source)
            if name == "Sorry":
                self.compile(str(path.relative_to(self.project)), expected="nonzero", output=False)
                self.compile(str(path.relative_to(self.project)), strict=False)
            else:
                self.compile(str(path.relative_to(self.project)))
            data = self.audit(["ReviewControls." + name], "control-" + name + ".json", kernel=(name == "Good"),
                              expected=0 if name == "Good" else "nonzero")
            if name == "Good":
                assert not data["failures"]
                assert all(not d["unsafe_dependencies"] for d in data["declarations"] if not d["unsafe"])
            elif name == "Unsafe": assert any("unsafe dependency" in item for item in data["failures"])
            else: assert any("forbidden axiom" in item for item in data["failures"])
            results.append({"fixture":name,"expected_rejected":name != "Good", "failures":data["failures"]})
        save(self.out / "control-results.json", results)
        return results

    def prepare(self):
        self.run([self.leanbin / "lean", "--version"])
        self.run([self.leanbin / "lake", "--version"])
        self.inspector()
        controls = self.controls()
        save(self.out / "summary.json", {"status":"PREPARATION_PASS", "author_proof_accessed":False,
             "controls":controls,"inspector_sha256":sha(self.project/"Verification/ClosureAudit.lean"),
             "limitation":"Only operational fixtures were compiled. No conjecture proof was read or validated."})

    def verify(self, submission, frozen):
        submission, frozen = P(submission).absolute(), P(frozen).absolute()
        selected_manifest_hash = sha(frozen)
        raw = json.loads(frozen.read_text())
        if "files" in raw:
            manifest = raw["files"]
            if isinstance(manifest,list): manifest = {entry["path"]:entry["sha256"] for entry in manifest}
            declaration = {**raw,"files":manifest}
        else:
            manifest = raw
            declaration = {"files":manifest}
        shutil.copy2(frozen,self.out/"selected-manifest.json")
        assert isinstance(manifest, dict) and manifest
        for name, digest in manifest.items():
            rel = P(name)
            assert not rel.is_absolute() and ".." not in rel.parts
            assert (submission / rel).resolve().is_relative_to(submission.resolve())
            assert re.fullmatch("[a-f0-9]{64}", digest) and sha(submission/rel) == digest
        save(self.out/"frozen-manifest.json", declaration)
        lean_sources = []
        for directory, names, files in os.walk(submission):
            names[:] = [n for n in names if n not in {".lake", ".git", "evidence"}]
            lean_sources += [str((P(directory)/f).relative_to(submission)) for f in files if f.endswith(".lean")]
        lean_sources.sort()
        assert lean_sources and all(f in manifest for f in lean_sources)
        assert all(P(f).parts[0] not in RESERVED for f in lean_sources)
        modules = [str(P(f).with_suffix("")).replace("/", ".") for f in lean_sources if f != "lakefile.lean"]
        assert all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*",m) for m in modules)
        findings = []
        for name in lean_sources:
            for line, text in enumerate(code_only((submission/name).read_text()).splitlines(),1):
                if FORBIDDEN.search(text): findings.append({"file":name,"line":line,"code":text})
        save(self.out/"active-source-token-audit.json", findings)
        assert not findings, "Forbidden token requires explicit reviewer repair/rejection"
        for name in set(lean_sources) | {"lake-manifest.json", "lean-toolchain"}:
            assert name in manifest
            dest = self.project/name; dest.parent.mkdir(parents=True,exist_ok=True)
            shutil.copy2(submission/name,dest)
        assert (self.project/"lean-toolchain").read_text().strip() == "leanprover/lean4:v4.19.0"
        package_manifest = json.loads((self.project/"lake-manifest.json").read_text())
        assert package_manifest["packagesDir"] == ".lake/packages"
        for spec in package_manifest["packages"]:
            assert spec["type"] == "git" and re.fullmatch("[a-f0-9]{40}",spec["rev"])
        self.run([self.leanbin/"lean","--version"])
        self.run([self.leanbin/"lake","--version"])
        packages = self.project/".lake/packages"; packages.mkdir()
        self.run(["/bin/cp","-cR",str(self.stock.resolve())+"/.",packages/"mathlib"])
        for spec in package_manifest["packages"]:
            if spec["name"] != "mathlib":
                self.run(["/bin/cp","-cR",packages/"mathlib/.lake/packages"/spec["name"],packages/spec["name"]])
        identities, index_before = [], {}
        for spec in package_manifest["packages"]:
            name = spec["name"]
            src = self.stock if name == "mathlib" else self.stock/".lake/packages"/name
            dst = packages/name
            if (src/".git/index").is_file(): index_before[name] = sha(src/".git/index")
            head = self.run(["/usr/bin/git","rev-parse","HEAD"],cwd=src).strip()
            assert head == spec["rev"]
            assert not self.run(["/usr/bin/git","status","--porcelain","--untracked-files=no"],cwd=src).strip()
            rows = []
            for relative in filter(None,self.run(["/usr/bin/git","ls-files","-z"],cwd=src).split("\0")):
                if (src/relative).is_file():
                    digest = sha(src/relative); assert sha(dst/relative) == digest
                    rows.append({"file":relative,"sha256":digest})
            save(self.out/"stock"/(name+".json"),rows)
            identities.append({"package":name,"revision":head,"tracked_files":len(rows),
                               "inventory_sha256":sha(self.out/"stock"/(name+".json"))})
        save(self.out/"package-identities.json",identities)
        # No authored compiled artifact was copied. Empty review library existed only
        # to configure the future inspector; it still has no files at this point.
        assert not any(self.lib.rglob("*.olean"))
        self.env.pop("LEAN_PATH",None)
        # Lake sees complete private dependency clones. Disable cache downloads
        # and reject any unexpected Git write/network or network downloader.
        offline = self.out/"offline-bin"; offline.mkdir()
        (offline/"git").write_text('#!/bin/sh\ncase "$1" in rev-parse|status|ls-files|describe|diff|log|show) exec /usr/bin/git "$@" ;; esac\nprintf "%s\\n" "Offline review rejected unexpected Git operation" >&2\nexit 97\n')
        (offline/"git").chmod(0o755)
        for tool in ["curl","wget","ssh","scp","ftp"]:
            (offline/tool).write_text('#!/bin/sh\nprintf "%s\\n" "Offline review rejected network tool" >&2\nexit 97\n')
            (offline/tool).chmod(0o755)
        self.env["PATH"] = str(offline)+":"+self.env["PATH"]
        self.run([self.leanbin/"lake","--no-cache","--wfail","build"])
        if "lakefile.lean" in lean_sources:
            self.run([self.leanbin/"lake","env","lean","-DwarningAsError=true","lakefile.lean"])
        # Use the explicitly known cache paths after Lake's project build.
        self.module_paths = [packages/spec["name"]/".lake/build/lib/lean" for spec in package_manifest["packages"]]
        self.env["LEAN_PATH"] = ":".join(map(str,[self.lib,*self.module_paths]))
        # Direct source replay creates fresh modules even if not in Lake's defaults.
        # Lake-built library modules are already available; nondefault auxiliaries
        # are compiled in import-dependency order, rejecting cycles/missing sources.
        remaining = set(modules); compiled = set()
        while remaining:
            ready = []
            for module in sorted(remaining):
                content = code_only((self.project/P(*module.split("."))).with_suffix(".lean").read_text())
                imports = re.findall(r"(?m)^\s*import\s+([A-Za-z_][A-Za-z_0-9.]*)",content)
                if not (set(imports) & remaining): ready.append(module)
            assert ready, "Cyclic authored module dependency"
            for module in ready:
                self.compile(str(P(*module.split(".")).with_suffix(".lean")))
                remaining.remove(module); compiled.add(module)
        self.inspector()
        data = self.audit(modules,"declaration-audit.json")
        assert not data["failures"]
        roots = {d["name"]:d for d in data["declarations"]}
        for name in declaration.get("capstones",[]):
            assert name in roots and not roots[name]["unsafe"]
        assert all(set(d["axioms"]) <= PERMITTED and not d["unsafe_dependencies"]
                   for d in roots.values() if not d["unsafe"])
        imported = []
        for module in data["imported_modules"]:
            if module in modules or module == "Verification.ClosureAudit": continue
            relative = P(*module.split(".")).with_suffix(".olean")
            matches = []
            for spec in package_manifest["packages"]:
                name = spec["name"]; original = self.stock if name == "mathlib" else self.stock/".lake/packages"/name
                copied = packages/name/".lake/build/lib/lean"/relative
                if copied.is_file():
                    digest = sha(copied); assert digest == sha(original/".lake/build/lib/lean"/relative)
                    source = original/relative.with_suffix(".lean")
                    matches.append({"module":module,"package":name,"olean_sha256":digest,
                                    "source_sha256":sha(source) if source.is_file() else None})
            assert len(matches) <= 1, "Ambiguous import identity"
            if not matches:
                runtime = self.leanbin.parent/"lib/lean"/relative
                assert runtime.is_file(), "Unbound imported module: " + module
                matches.append({"module":module,"package":"Lean-runtime","olean_sha256":sha(runtime)})
            imported += matches
        save(self.out/"import-identities.json",imported)
        controls = self.controls()
        runtime_helpers = [d for d in roots.values() if d["unsafe"]]
        save(self.out/"runtime-helper-inventory.json",runtime_helpers)
        assert all(sha(submission/f)==digest for f,digest in manifest.items()), "Submission changed during review"
        assert sha(frozen) == selected_manifest_hash, "Selected manifest changed during review"
        index_checks = []
        for name, before in index_before.items():
            src = self.stock if name == "mathlib" else self.stock/".lake/packages"/name
            after = sha(src/".git/index")
            index_checks.append({"package":name,"before":before,"after":after,"unchanged":before==after})
        save(self.out/"stock-index-stability.json",index_checks)
        assert all(item["unchanged"] for item in index_checks), "Stock index changed during review"
        save(self.out/"summary.json",{"status":"PASS_PENDING_RUNTIME_HELPER_CLASSIFICATION" if runtime_helpers else "PASS",
            "frozen_manifest_sha256":sha(frozen),"modules":modules,"package_identities":identities,
            "import_identity_count":len(imported),"local_declaration_count":data["local_declaration_count"],
            "closure_declaration_count":data["closure_declaration_count"],"capstones":declaration.get("capstones",[]),
            "audit_failures":data["failures"],"runtime_helper_count":len(runtime_helpers),"controls":controls,
            "limits":["Cached dependency imports byte-matched supplied stock; full Mathlib was not rebuilt.",
                      "Supplied Lean runtime was not bootstrapped.","Semantic and PDF review are separate.",
                      "Unsafe generated runtime declarations are inventoried separately and require explicit classification if present."]})


if __name__ == "__main__":
    if len(sys.argv) == 5 and sys.argv[1] == "prepare":
        review = Review(*sys.argv[2:]); review.prepare()
    elif len(sys.argv) == 7 and sys.argv[1] == "verify":
        review = Review(*sys.argv[4:]); review.verify(*sys.argv[2:4])
    else:
        raise SystemExit(__doc__)
