"""Focused offline regressions; all mutable fixtures stay in the worker audit directory."""
from __future__ import annotations

from contextlib import redirect_stdout
from fractions import Fraction
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

PACKAGE = Path(__file__).absolute().parents[1]
AUDIT = Path("D:/AStudy/" + "\u5f00\u6e90\u6742" + "/LastMathC/.local/audits/23-reproducer-20261013")
SPEC = importlib.util.spec_from_file_location("reproduce23", PACKAGE / "reproduce.py")
assert SPEC is not None and SPEC.loader is not None
sys.dont_write_bytecode = True
r = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(r)


class ReproducerTests(unittest.TestCase):
    def setUp(self):
        AUDIT.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="focused-", dir=AUDIT)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.package = self.root / "package"
        self.lean = self.package / "lean4"
        self.lean.mkdir(parents=True)
        for name in (*[n + ".lean" for n in r.ROOTS], "lakefile.lean", "lean-toolchain", "lake-manifest.json"):
            shutil.copyfile(PACKAGE / "lean4" / name, self.lean / name)
        for name in ("submission.json", "source.md"):
            shutil.copyfile(PACKAGE / name, self.package / name)
        self.manifest = json.loads((self.package / "submission.json").read_text(encoding="utf-8-sig"))
        self.names = self.manifest["theorems"]
        self.repo = self.root / "repo"
        (self.repo / "conjectures").mkdir(parents=True)
        self.raw = (self.package / "source.md").read_bytes()
        self.current = self.repo / "conjectures" / (r.CID + ".md")
        self.current.write_bytes(self.raw)
        self.addCleanup(setattr, r, "LAKE_BIN", r.LAKE_BIN)

    def source_git(self, repo, *args):
        return {("cat-file", "-t", r.SOURCE_COMMIT): b"commit\n",
                ("rev-parse", r.SOURCE_COMMIT + ":conjectures/" + r.CID + ".md"): r.SOURCE_BLOB.encode() + b"\n",
                ("cat-file", "-t", r.SOURCE_BLOB): b"blob\n",
                ("cat-file", "blob", r.SOURCE_BLOB): self.raw}[args]

    def check_source(self):
        with mock.patch.object(r, "git", side_effect=self.source_git):
            return r.validate_source(self.package, self.repo, self.manifest)

    def edit(self, name, old, new):
        path = self.lean / name
        data = path.read_text(encoding="utf-8")
        self.assertIn(old, data)
        path.write_text(data.replace(old, new, 1), encoding="utf-8")

    def check_lean(self):
        return r.validate_lean(self.lean, self.names)

    def dependencies(self):
        for spec in r.expected_lock()["packages"]:
            checkout = self.lean / ".lake" / "packages" / spec["name"]
            (checkout / ".git").mkdir(parents=True)
            (checkout / "source.lean").write_text("-- fixture\n", encoding="utf-8")

    def dependency_git(self, repo, *args):
        spec = next(s for s in r.expected_lock()["packages"] if s["name"] == repo.name)
        data = b"-- fixture\n"
        oid = r.hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest().encode()
        outputs = {
            ("rev-parse", "--show-toplevel"): str(repo).encode(),
            ("rev-parse", "--absolute-git-dir"): str(repo / ".git").encode(),
            ("rev-parse", "HEAD"): spec["rev"].encode(),
            ("remote", "get-url", "origin"): spec["url"].encode(),
            ("status", "--porcelain=v1", "-z", "--untracked-files=no", "--ignore-submodules=none"): b"",
            ("ls-files", "--stage", "-z"): b"100644 " + oid + b" 0\tsource.lean\0",
            ("ls-tree", "-r", "-z", "--full-tree", "HEAD"): b"100644 blob " + oid + b"\tsource.lean\0",
        }
        return outputs[args]

    def check_dependencies(self, override=None):
        def response(repo, *args):
            if override is not None:
                result = override(repo, args)
                if result is not None:
                    return result
            return self.dependency_git(repo, *args)
        with mock.patch.object(r, "git", side_effect=response):
            return r.materialized_dependencies(self.lean, r.expected_lock())

    def test_real_five_module_inventory(self):
        inventory = self.check_lean()
        self.assertEqual(inventory["count"], 36)
        self.assertEqual([len(v) for v in inventory["modules"].values()], [14, 5, 8, 5, 4])

    def test_manifest_inventory_missing_extra_duplicate_or_same_count_replacement(self):
        for names in (self.names[:-1], self.names + [self.names[0]],
                      self.names[:-1] + ["SUnit23.not_advertised"], list(reversed(self.names))):
            with self.subTest(names=names[-1]):
                if set(names) == set(self.names) and len(names) == 36:
                    self.assertEqual(r.theorem_names({"theorems": names}), names)
                else:
                    with self.assertRaises(r.ReproductionError):
                        r.theorem_names({"theorems": names})

    def test_public_theorem_missing_from_manifest(self):
        self.edit("RatBridge.lean", "end SUnit23", "theorem unadvertised : True := by trivial\nend SUnit23")
        with self.assertRaises(r.ReproductionError):
            self.check_lean()

    def test_renamed_theorem_not_masked_by_comment(self):
        self.edit("RatBridge.lean", "theorem reduced_num", "-- theorem reduced_num\ntheorem replaced_num")
        with self.assertRaises(r.ReproductionError):
            self.check_lean()

    def test_lemma_is_in_public_inventory(self):
        self.edit("RatBridge.lean", "theorem reduced_num", "lemma reduced_num")
        self.assertEqual(self.check_lean()["count"], 36)

    def test_extra_authored_module_rejected(self):
        (self.lean / "Injected.lean").write_text("import Main\n", encoding="utf-8")
        with self.assertRaises(r.ReproductionError):
            self.check_lean()

    def test_check_comment_does_not_count_as_check(self):
        self.edit("Check.lean", "#check " + self.names[0], "-- #check " + self.names[0])
        with self.assertRaises(r.ReproductionError):
            self.check_lean()

    def test_check_duplicate_print_rejected(self):
        self.edit("Check.lean", "#print axioms " + self.names[0],
                  ("#print axioms " + self.names[0] + "\n") * 2)
        with self.assertRaises(r.ReproductionError):
            self.check_lean()

    def test_check_unsafe_commands_and_inexact_names_rejected(self):
        check = self.lean / "Check.lean"
        original = check.read_text(encoding="utf-8")
        for extra in ("#eval 1", "set_option warningAsError false", "import Mathlib", "#check " + self.names[0] + "Extra",
                      "#print axioms SUnit23.extra", "#print prefix SUnit23", "#check True", "#exit", "theorem hidden : True := by trivial"):
            with self.subTest(extra=extra):
                check.write_text(original + "\n" + extra + "\n", encoding="utf-8")
                with self.assertRaises(r.ReproductionError):
                    self.check_lean()

    def test_safe_definition_print_and_nested_comments(self):
        check = self.lean / "Check.lean"
        with check.open("a", encoding="utf-8") as stream:
            stream.write("\n/- outer /- nested -/ #eval 4 -/\n#print " + self.names[0] + "\n")
        self.assertEqual(self.check_lean()["count"], 36)
        with self.assertRaises(r.ReproductionError):
            r.scrub_comments("/- unterminated")

    def test_source_raw_and_current_crlf(self):
        self.current.write_bytes(self.raw.replace(b"\n", b"\r\n"))
        self.assertEqual(self.check_source()["commit"], r.SOURCE_COMMIT)

    def test_source_fixed_commit_blob_and_sha(self):
        for key in ("source_commit", "source_git_blob", "source_sha256"):
            with self.subTest(key=key):
                saved = self.manifest[key]
                self.manifest[key] = "0" * len(saved)
                with self.assertRaises(r.ReproductionError):
                    self.check_source()
                self.manifest[key] = saved

    def test_source_commit_tree_binding(self):
        def wrong(repo, *args):
            return b"0" * 40 if args[0] == "rev-parse" else self.source_git(repo, *args)
        with mock.patch.object(r, "git", side_effect=wrong), self.assertRaises(r.ReproductionError):
            r.validate_source(self.package, self.repo, self.manifest)

    def test_frozen_raw_and_current_semantic_tampering(self):
        self.current.write_bytes(self.raw + b"\nchanged\n")
        with self.assertRaises(r.ReproductionError):
            self.check_source()
        self.current.write_bytes(self.raw)
        (self.package / "source.md").write_bytes(self.raw.replace(b"\n", b"\r\n"))
        with self.assertRaises(r.ReproductionError):
            self.check_source()

    def test_exact_lake_declarative_configuration(self):
        self.assertEqual(r.validate_config(self.lean), r.expected_lock())
        self.edit("lakefile.lean", "-DwarningAsError=true", "-DwarningAsError=false")
        with self.assertRaises(r.ReproductionError):
            r.validate_config(self.lean)

    def test_lake_roots_or_executable_configuration_rejected(self):
        lakefile = self.lean / "lakefile.lean"
        original = lakefile.read_text(encoding="utf-8")
        for text in (original.replace(", " + chr(96) + "Check", ""), original + "\ninitialize IO.println 1\n"):
            lakefile.write_text(text, encoding="utf-8")
            with self.assertRaises(r.ReproductionError):
                r.validate_config(self.lean)

    def test_all_nine_dependency_pins_and_manifest_paths_exact(self):
        path = self.lean / "lake-manifest.json"
        for index in range(9):
            lock = r.expected_lock()
            lock["packages"][index]["rev"] = "0" * 40
            path.write_text(json.dumps(lock), encoding="utf-8")
            with self.subTest(index=index), self.assertRaises(r.ReproductionError):
                r.validate_config(self.lean)
        for key, value in (("packagesDir", "../packages"), ("lakeDir", "../cache")):
            lock = r.expected_lock()
            lock[key] = value
            path.write_text(json.dumps(lock), encoding="utf-8")
            with self.assertRaises(r.ReproductionError):
                r.validate_config(self.lean)

    def test_physical_nine_checkouts(self):
        self.dependencies()
        self.assertEqual(len(self.check_dependencies()), 9)

    def test_missing_dotgit_cannot_inherit_parent(self):
        self.dependencies()
        checkout = self.lean / ".lake" / "packages" / "mathlib"
        (checkout / ".git").rmdir()
        with mock.patch.object(r, "git") as git, self.assertRaises(r.ReproductionError):
            r.materialized_dependencies(self.lean, r.expected_lock())
        git.assert_not_called()

    def test_dotgit_file_cannot_redirect_checkout(self):
        self.dependencies()
        path = self.lean / ".lake" / "packages" / "mathlib" / ".git"
        path.rmdir()
        path.write_text("gitdir: ../../other\n", encoding="utf-8")
        with self.assertRaises(r.ReproductionError):
            self.check_dependencies()

    def test_dependency_head_origin_dirty_parent_or_metadata_redirect(self):
        self.dependencies()
        for command, output in ((("rev-parse", "HEAD"), b"0" * 40),
                                (("remote", "get-url", "origin"), b"https://example.invalid/wrong"),
                                (("rev-parse", "--show-toplevel"), str(self.lean).encode()),
                                (("rev-parse", "--absolute-git-dir"), str(self.root).encode()),
                                (("status", "--porcelain=v1", "-z", "--untracked-files=no", "--ignore-submodules=none"), b" M source.lean\0")):
            with self.subTest(command=command), self.assertRaises(r.ReproductionError):
                self.check_dependencies(lambda repo, args: output if args == command else None)

    def test_tracked_symlink_gitlink_unmerged_or_traversal(self):
        self.dependencies()
        for record in (b"120000 a 0\tsource.lean\0", b"160000 a 0\tsource.lean\0",
                       b"100644 a 1\tsource.lean\0", b"100644 a 0\t../../../../../source.md\0"):
            with self.subTest(record=record), self.assertRaises(r.ReproductionError):
                self.check_dependencies(lambda repo, args: record if args == ("ls-files", "--stage", "-z") else None)

    def test_dependency_bytes_hidden_from_status_and_index_tree_mismatch(self):
        self.dependencies()
        source = self.lean / ".lake" / "packages" / "mathlib" / "source.lean"
        source.write_bytes(b"-- tampered despite clean-status response\n")
        with self.assertRaisesRegex(r.ReproductionError, "bytes changed"):
            self.check_dependencies()
        source.write_bytes(b"-- fixture\r\n")
        self.assertEqual(len(self.check_dependencies()), 9)
        with self.assertRaisesRegex(r.ReproductionError, "index differs"):
            self.check_dependencies(lambda repo, args: b"" if args == ("ls-tree", "-r", "-z", "--full-tree", "HEAD") else None)

    def test_pinned_windows_inertlink_text_not_arbitrary_symlinks(self):
        for name, entries in r.WINDOWS_LINKTEXT.items():
            for relative in entries:
                self.assertEqual(r.dependency_mode_allowed(name, b"120000", relative), os.name == "nt")
                self.assertFalse(r.dependency_mode_allowed("aesop", b"120000", relative))
        self.assertFalse(r.dependency_mode_allowed("mathlib", b"120000", b"Mathlib/Injected.lean"))
        self.assertFalse(r.dependency_mode_allowed("batteries", b"120000", b"docs/UNEXPECTED.md"))
        self.dependencies()
        # Exercise exact link-text contents, not just the mode whitelist.
        contents = {("mathlib", b"scripts/bench/build/fake-root/bin/lean.py"): b"lean",
                    ("mathlib", b"scripts/bench/size/run.py"): b"run",
                    ("batteries", b"docs/README.md"): b"../README.md"}
        for (name, relative), data in contents.items():
            path = self.lean / ".lake" / "packages" / name / relative.decode()
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        def extra(repo, args):
            if repo.name not in r.WINDOWS_LINKTEXT:
                return None
            entries = r.WINDOWS_LINKTEXT[repo.name]
            if args == ("ls-files", "--stage", "-z"):
                return self.dependency_git(repo, *args) + b"".join(b"120000 " + oid + b" 0\t" + relative + b"\0" for relative, oid in entries.items())
            if args == ("ls-tree", "-r", "-z", "--full-tree", "HEAD"):
                return self.dependency_git(repo, *args) + b"".join(b"120000 blob " + oid + b"\t" + relative + b"\0" for relative, oid in entries.items())
            return None
        if os.name == "nt":
            self.assertEqual(len(self.check_dependencies(extra)), 9)
            for (name, relative), data in contents.items():
                path = self.lean / ".lake" / "packages" / name / relative.decode()
                path.write_bytes(b"changed")
                with self.assertRaisesRegex(r.ReproductionError, "link-text placeholder changed"):
                    self.check_dependencies(extra)
                path.write_bytes(data)
        else:
            with self.assertRaises(r.ReproductionError):
                self.check_dependencies(extra)

    def test_environment_removes_secrets_lean_and_git_injection(self):
        synthetic = {"PATH": "local", "Gh_ToKeN": "sentinel", "GITHUB_TOKEN": "sentinel", "OPENAI_API_KEY": "sentinel",
                     "CUSTOM_SECRET": "sentinel", "OTHER_TOKEN": "sentinel", "PASSWORD": "sentinel", "LEAN_PATH": "injected",
                     "LEAN_SRC_PATH": "injected", "GIT_DIR": "parent", "GIT_CONFIG_COUNT": "9", "GIT_CONFIG_KEY_8": "injected",
                     "MATHLIB_NO_CACHE_ON_UPDATE": "0", "OK": "kept"}
        with mock.patch.dict(os.environ, synthetic, clear=True):
            env = r.child_env()
        self.assertNotIn("sentinel", env.values())
        self.assertNotIn("LEAN_PATH", env)
        self.assertNotIn("LEAN_SRC_PATH", env)
        self.assertNotIn("GIT_DIR", env)
        self.assertNotIn("GIT_CONFIG_KEY_8", env)
        self.assertEqual(env["MATHLIB_NO_CACHE_ON_UPDATE"], "1")
        self.assertEqual(env["GIT_CONFIG_VALUE_0"], "")
        self.assertEqual(env["GIT_CONFIG_KEY_0"], "credential.helper")
        self.assertEqual(env["GIT_NO_LAZY_FETCH"], "1")

    def test_git_never_enables_manager_helper(self):
        with mock.patch.object(r, "run", return_value=b"") as run:
            r.git(self.repo, "rev-parse", "HEAD")
        self.assertIn("credential.helper=", run.call_args.args[0])
        self.assertNotIn("credential.helper=manager", run.call_args.args[0])

    def test_run_raw_stdout_not_stderr_and_no_secret_error_echo(self):
        result = SimpleNamespace(returncode=0, stdout=b"raw\r\n", stderr=b"warning\n")
        with mock.patch.object(subprocess, "run", return_value=result):
            self.assertEqual(r.run(["git", "cat-file"], self.repo), b"raw\r\n")
        result.returncode = 9
        result.stderr = b"secret sentinel"
        with mock.patch.object(subprocess, "run", return_value=result), self.assertRaises(r.ReproductionError) as error:
            r.run(["git", "cat-file"], self.repo)
        self.assertNotIn("sentinel", str(error.exception))
        self.assertIn("exit 9", str(error.exception))

    def test_exact_project_only_cache_cleanup(self):
        build = self.lean / ".lake" / "build"
        build.mkdir(parents=True)
        (build / "artifact").write_text("generated", encoding="utf-8")
        packages = self.lean / ".lake" / "packages"
        packages.mkdir()
        keep = packages / "keep"
        keep.write_text("keep", encoding="utf-8")
        with self.assertRaises(r.ReproductionError):
            r.clean_project_build(self.lean, packages)
        self.assertTrue((build / "artifact").exists())
        r.clean_project_build(self.lean)
        self.assertFalse(build.exists())
        self.assertEqual(keep.read_text(encoding="utf-8"), "keep")

    def test_cache_refuses_every_reparse_ancestor_and_descendant(self):
        build = self.lean / ".lake" / "build"
        nested = build / "nested"
        nested.mkdir(parents=True)
        (nested / "keep").write_text("generated", encoding="utf-8")
        original = Path.lstat
        for rejected in (self.lean / ".lake", build, nested):
            def inspect(path, *args, **kwargs):
                if path == rejected:
                    return SimpleNamespace(st_mode=stat.S_IFDIR, st_file_attributes=0x400)
                return original(path, *args, **kwargs)
            with self.subTest(rejected=rejected), mock.patch.object(Path, "lstat", inspect), self.assertRaises(r.ReproductionError):
                r.clean_project_build(self.lean)
            self.assertTrue((nested / "keep").exists())

    def test_actual_junction_or_symlink_preserves_external_target(self):
        outside = self.root / "outside"
        outside.mkdir()
        sentinel = outside / "keep"
        sentinel.write_text("keep", encoding="utf-8")
        build = self.lean / ".lake" / "build"
        build.mkdir(parents=True)
        link = build / "linked"
        if os.name == "nt":
            result = subprocess.run(["cmd", "/c", "mklink", "/J", str(link), str(outside)],
                                    env=r.child_env(), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            self.assertEqual(result.returncode, 0, "Local junction fixture creation failed")
        else:
            link.symlink_to(outside, target_is_directory=True)
        try:
            with self.assertRaises(r.ReproductionError):
                r.safe_path(link)
            with self.assertRaises(r.ReproductionError):
                r.clean_project_build(self.lean)
            self.assertEqual(sentinel.read_text(encoding="utf-8"), "keep")
        finally:
            if os.name == "nt":
                os.rmdir(link)
            else:
                link.unlink()

    def test_freeze_detects_changed_added_removed_files_not_project_cache(self):
        before = r.frozen_files(self.package)
        cache = self.lean / ".lake" / "build"
        cache.mkdir(parents=True)
        (cache / "generated").write_text("ignored", encoding="utf-8")
        self.assertEqual(r.frozen_files(self.package), before)
        path = self.package / "submission.json"
        original = path.read_bytes()
        path.write_bytes(original + b"\n")
        self.assertNotEqual(r.frozen_files(self.package), before)
        path.write_bytes(original)
        extra = self.package / "added"
        extra.write_text("new", encoding="utf-8")
        self.assertNotEqual(r.frozen_files(self.package), before)
        extra.unlink()
        path.unlink()
        self.assertNotEqual(r.frozen_files(self.package), before)

    def test_all_axioms_exact_missing_duplicate_unknown_nonstandard_and_malformed(self):
        valid = "\n".join("'" + name + "' depends on axioms: [propext, Classical.choice, Quot.sound]" for name in self.names)
        self.assertEqual(len(r.audit_axioms(valid, self.names)), 36)
        for output in ("\n".join(valid.splitlines()[:-1]), valid + "\n" + valid.splitlines()[0],
                       valid + "\n'SUnit23.extra' does not depend on any axioms", valid.replace("propext", "sorryAx", 1),
                       valid.replace("[propext, Classical.choice, Quot.sound]", "[propext,]", 1),
                       valid.replace("depends on axioms:", "depends on axiom:", 1)):
            with self.subTest(output=output[-60:]), self.assertRaises(r.ReproductionError):
                r.audit_axioms(output, self.names)

    def test_exact_python_support_zero_negative_reduced_and_ordered(self):
        self.assertEqual(r.prime_support(1), set())
        self.assertEqual(r.prime_support(-360), {2, 3, 5})
        self.assertFalse(r.is_sunit({2, 3, 5, 7}, Fraction(0)))
        self.assertTrue(r.is_sunit({2, 3, 5, 7}, Fraction(-6, 35)))
        self.assertFalse(r.is_sunit({2, 3, 5}, Fraction(1, 7)))
        self.assertEqual(Fraction(1, 2), Fraction(2, 4))
        self.assertNotEqual((Fraction(1, 3), Fraction(2, 3)), (Fraction(2, 3), Fraction(1, 3)))
        report = r.regression()
        self.assertEqual([s["N"] for s in report["samples"]], list(range(33)) + [64])
        rows = {s["N"]: s for s in report["samples"]}
        self.assertEqual([rows[n]["coprime_pairs"] for n in (0, 1, 2, 3, 4, 8, 16)], [0, 1, 3, 7, 11, 43, 159])
        self.assertTrue(all(s["coprime_pairs"] == s["rational_witnesses"] for s in rows.values()))

    def workflow(self, changed=False, build_fails=False, skip_update=True):
        baseline = {"source": {}, "lock": r.expected_lock(), "theorems": {"names": self.names}, "files": {"manifest": "old"}}
        after = {**baseline, "files": {"manifest": "changed"}} if changed else baseline
        audit = "\n".join("'" + n + "' does not depend on any axioms" for n in self.names).encode()
        def tools(args, cwd, timeout=120, show_output=False):
            if args[-1] == "--version":
                return b"Lake version 5.0.0-src+abcdef (Lean version 4.33.1)\n" if len(args) == 2 else b"Lean (version 4.33.1, fixture)\n"
            if "build" in args and build_fails:
                raise r.ReproductionError("synthetic build failure")
            return audit if args[-1] == "Check.lean" else b""
        with mock.patch.object(r, "preflight", side_effect=[baseline, baseline, after]) as preflight, \
             mock.patch.object(r, "materialized_dependencies", return_value={"count": 9}) as dependencies, \
             mock.patch.object(r, "regression", return_value={}), \
             mock.patch.object(shutil, "which", return_value=str(PACKAGE / "reproduce.py")), \
             mock.patch.object(r, "run", side_effect=tools) as run, \
             mock.patch.object(r, "clean_project_build") as cleanup, redirect_stdout(io.StringIO()):
            result = r.reproduce(self.package, self.repo, "lake", skip_update)
        return result, run, preflight, dependencies, cleanup

    def test_offline_runs_all_replays_and_dependency_audits_without_update(self):
        result, run, preflight, dependencies, cleanup = self.workflow()
        commands = [call.args[0] for call in run.call_args_list]
        self.assertTrue(all("--offline" in c for c in commands if c[1:] != ["--version"]))
        self.assertTrue(all("update" not in c and "fetch" not in c for c in commands))
        self.assertTrue(any("--wfail" in c and "build" in c for c in commands))
        replays = [c[-1] for c in commands if c[-1].endswith(".lean")]
        self.assertEqual(replays, [m + ".lean" for m in (*r.MODULES, "Main", "Check")])
        self.assertEqual(preflight.call_count, 3)
        self.assertEqual(dependencies.call_count, 2)
        cleanup.assert_called_once_with(self.lean)
        self.assertEqual(result["status"], "PASS")

    def test_workflow_freeze_violation_blocks_success(self):
        with self.assertRaisesRegex(r.ReproductionError, "Frozen authored files"):
            self.workflow(changed=True)

    def test_update_mode_only_materializes_after_validated_lock_then_updates(self):
        result, run, preflight, dependencies, cleanup = self.workflow(skip_update=False)
        commands = [call.args[0] for call in run.call_args_list]
        self.assertEqual(commands[1][1:], ["update"])
        self.assertEqual(dependencies.call_count, 2)
        self.assertEqual(preflight.call_count, 3)
        self.assertEqual(result["status"], "PASS")

    def test_failed_build_is_not_reported_as_pass(self):
        with self.assertRaisesRegex(r.ReproductionError, "synthetic build failure"):
            self.workflow(build_fails=True)

    def test_dependency_block_still_checks_frozen_files_and_never_cleans(self):
        baseline = {"lock": r.expected_lock(), "files": {"manifest": "unchanged"}}
        with mock.patch.object(r, "preflight", return_value=baseline) as preflight, \
             mock.patch.object(r, "materialized_dependencies", side_effect=r.ReproductionError("dependency BLOCK")), \
             mock.patch.object(r, "run") as run, mock.patch.object(r, "clean_project_build") as cleanup, \
             self.assertRaisesRegex(r.ReproductionError, "dependency BLOCK"):
            r.reproduce(self.package, self.repo, "lake", True)
        self.assertEqual(preflight.call_count, 2)
        run.assert_not_called()
        cleanup.assert_not_called()

    def test_path_cache_never_skips_entry_lstat_and_fresh_pass_checks_ancestors(self):
        parent = self.root / "cached-parent"
        parent.mkdir()
        child = parent / "child"
        child.write_bytes(b"entry")
        checked = set()
        r.safe_path(parent, checked)
        original = Path.lstat
        seen = []
        def inspect(path, *args, **kwargs):
            seen.append(path)
            if path == child:
                return SimpleNamespace(st_mode=stat.S_IFREG, st_file_attributes=0x400)
            return original(path, *args, **kwargs)
        with mock.patch.object(Path, "lstat", inspect), self.assertRaises(r.ReproductionError):
            r.safe_path(child, checked)
        self.assertIn(child, seen)
        self.assertNotIn(parent, seen)
        def changed_parent(path, *args, **kwargs):
            if path == parent:
                return SimpleNamespace(st_mode=stat.S_IFDIR, st_file_attributes=0x400)
            return original(path, *args, **kwargs)
        with mock.patch.object(Path, "lstat", changed_parent), self.assertRaises(r.ReproductionError):
            r.safe_path(child, set())

    def test_cli_configures_utf8_before_lean_output(self):
        stdout, stderr = mock.Mock(), mock.Mock()
        argv = ["reproduce.py", "--repo", str(self.repo), "--lake", "lake", "--skip-update"]
        with mock.patch.object(sys, "stdout", stdout), mock.patch.object(sys, "stderr", stderr), \
             mock.patch.object(sys, "argv", argv), mock.patch.object(r, "reproduce", return_value={"status": "PASS"}):
            self.assertEqual(r.main(), 0)
        stdout.reconfigure.assert_called_once_with(encoding="utf-8", errors="backslashreplace")
        stderr.reconfigure.assert_called_once_with(encoding="utf-8", errors="backslashreplace")


if __name__ == "__main__":
    unittest.main()
