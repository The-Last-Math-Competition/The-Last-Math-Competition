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
AUDIT = Path(tempfile.gettempdir()) / "tlmc259-reproducer-tests"
SPEC = importlib.util.spec_from_file_location("reproduce259", PACKAGE / "reproduce.py")
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
        shutil.copyfile(PACKAGE / "source.md", self.package / "source.md")
        # Synthetic test manifest; never writes the coordinator's real manifest.
        self.manifest = {"id": r.CID, "solver": "idealistichacker",
                         "source_commit": r.SOURCE_COMMIT, "source_git_blob": r.SOURCE_BLOB,
                         "source_sha256": r.SOURCE_SHA256, "theorems": list(r.THEOREMS)}
        (self.package / "submission.json").write_text(json.dumps(self.manifest), encoding="utf-8")
        self.names = self.manifest["theorems"]
        self.repo = self.root / "repo"
        (self.repo / "conjectures").mkdir(parents=True)
        self.raw = (self.package / "source.md").read_bytes()
        self.current = self.repo / "conjectures" / (r.CID + ".md")
        self.current.write_bytes(self.raw)
        self.addCleanup(setattr, r, "LAKE_BIN", r.LAKE_BIN)
        self.addCleanup(setattr, r, "DEADLINE", r.DEADLINE)
        r.DEADLINE = None

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

    def test_real_three_module_inventory(self):
        inventory = self.check_lean()
        self.assertEqual(inventory["count"], 19)
        self.assertEqual([len(v) for v in inventory["modules"].values()], [4, 8, 7])

    def test_manifest_inventory_missing_extra_duplicate_or_same_count_replacement(self):
        for names in (self.names[:-1], self.names + [self.names[0]],
                      self.names[:-1] + ["PrimePell259.not_advertised"], list(reversed(self.names))):
            with self.subTest(names=names[-1]):
                if set(names) == set(self.names) and len(names) == 19:
                    self.assertEqual(r.theorem_names({"theorems": names}), names)
                else:
                    with self.assertRaises(r.ReproductionError):
                        r.theorem_names({"theorems": names})

    def test_public_theorem_missing_from_manifest(self):
        self.edit("PrimePell.lean", "end PrimePell259", "theorem unadvertised : True := by trivial\nend PrimePell259")
        with self.assertRaises(r.ReproductionError):
            self.check_lean()

    def test_renamed_theorem_not_masked_by_comment(self):
        self.edit("PrimePell.lean", "theorem pell_mod_four_parity", "-- theorem pell_mod_four_parity\ntheorem replaced_num")
        with self.assertRaises(r.ReproductionError):
            self.check_lean()

    def test_lemma_is_in_public_inventory(self):
        self.edit("PrimePell.lean", "theorem pell_mod_four_parity", "lemma pell_mod_four_parity")
        with self.assertRaisesRegex(r.ReproductionError, "raw hash mismatch"):
            self.check_lean()

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
                      "#print axioms PrimePell259.extra", "#print prefix PrimePell259", "#check True", "#exit", "theorem hidden : True := by trivial"):
            with self.subTest(extra=extra):
                check.write_text(original + "\n" + extra + "\n", encoding="utf-8")
                with self.assertRaises(r.ReproductionError):
                    self.check_lean()

    def test_safe_definition_print_and_nested_comments(self):
        check = self.lean / "Check.lean"
        with check.open("a", encoding="utf-8") as stream:
            stream.write("\n/- outer /- nested -/ #eval 4 -/\n")
        self.assertEqual(self.check_lean()["count"], 19)
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
        self.assertEqual(len(r.audit_axioms(valid, self.names)), 19)
        for output in ("\n".join(valid.splitlines()[:-1]), valid + "\n" + valid.splitlines()[0],
                       valid + "\n'PrimePell259.extra' does not depend on any axioms", valid.replace("propext", "sorryAx", 1),
                       valid.replace("[propext, Classical.choice, Quot.sound]", "[propext,]", 1),
                       valid.replace("depends on axioms:", "depends on axiom:", 1)):
            with self.subTest(output=output[-60:]), self.assertRaises(r.ReproductionError):
                r.audit_axioms(output, self.names)

    def test_exact_integer_and_product_regressions(self):
        report = r.regression()
        self.assertEqual(report['integer_certificates'], 5)
        self.assertEqual(report['finite_product_prefixes'], 80)
        self.assertIn('not the universal', report['boundary'])

    def test_hash_gate_checks_each_mathematical_module_raw_bytes(self):
        for module in r.MODULES:
            target = self.lean / (module + ".lean")
            data = target.read_bytes()
            for changed in (data + b"\n", data.replace(b"\n", b"\r\n")):
                target.write_bytes(changed)
                with self.subTest(module=module), self.assertRaisesRegex(r.ReproductionError, "raw hash mismatch"):
                    self.check_lean()
            target.write_bytes(data)

    def test_current_dialect_all_three_real_modules_and_normal_fields(self):
        for module, namespace in r.MODULES.items():
            code = r.scrub_comments((self.lean / (module + ".lean")).read_text(encoding="utf-8"))
            tree = r.source_commands(code, namespace, module)
            self.assertEqual(tree["public"], [n for n in self.names if n.startswith(namespace + ".")])
        code = """namespace Normal
noncomputable section
variable {K : Type*} [Field K]
class DataAndProp (K : Type*) where
  value : K
  proof : True
instance normalInstance : Inhabited Nat := by
  exact inferInstance
omit [Field K] in
theorem cases_ok : True := by
  cases True.intro
  case intro => trivial
end
end Normal
"""
        tree = r.source_commands(code, "Normal", "fixture")
        self.assertEqual(tree["public"], ["Normal.cases_ok"])

    def test_dialect_rejects_executable_extensions_and_namespace_tricks(self):
        code = "namespace Normal\ntheorem fine : True := by trivial\nend Normal\n"
        for extra in ("#eval 1", "elab danger : command => pure ()", "macro danger : command => pure ()",
                      "axiom injected : False", "unsafe def f := 1", "set_option warningAsError false",
                      "syntax danger : command", "attribute [simp] fine", "#print prefix Normal"):
            with self.subTest(extra=extra), self.assertRaises(r.ReproductionError):
                r.source_commands(code.replace("end Normal", extra + "\nend Normal"), "Normal", "fixture")
        for malformed in (code.replace("end Normal", "end Wrong"), code.replace("namespace Normal", "namespace Fake"),
                          "theorem fine : True := by trivial\n" + code):
            with self.assertRaises(r.ReproductionError):
                r.source_commands(malformed, "Normal", "fixture")

    def test_check_no_extra_print_hide_or_command_even_with_complete_inventory(self):
        target = self.lean / "Check.lean"
        data = target.read_text(encoding="utf-8")
        for extra in ("#print " + self.names[0], "#print axioms " + self.names[0],
                      "#eval 1", "set_option pp.universes false", "open PellDensity259", "namespace Hidden"):
            target.write_text(data + "\n" + extra, encoding="utf-8")
            with self.subTest(extra=extra), self.assertRaises(r.ReproductionError):
                self.check_lean()
        target.write_text(data, encoding="utf-8")

    def test_full_actual_types_reject_duplicates_missing_extra_and_malformed(self):
        blocks = [n + ".{u_1} {K : Type u_1} :\n  True\n'" + n + "' does not depend on any axioms"
                  for n in self.names]
        valid = "\n".join(blocks)
        self.assertEqual(set(r.audit_theorem_types(valid, self.names)), set(self.names))
        for invalid in ("\n".join(blocks[:-1]), valid + "\n" + blocks[0], valid + "\nextra diagnostic",
                        valid.replace(self.names[0] + ".{u_1}", "Unadvertised.fake", 1),
                        valid.replace("  True", "extra command", 1)):
            with self.assertRaises(r.ReproductionError):
                r.audit_theorem_types(invalid, self.names)

    def test_preflight_only_never_launches_lake_or_prepares_dependencies(self):
        argv = ["reproduce.py", "--repo", str(self.repo), "--lake", "lake", "--preflight-only"]
        with mock.patch.object(sys, "argv", argv), mock.patch.object(r, "preflight", return_value={}) as preflight, \
             mock.patch.object(r, "run") as run, mock.patch.object(r, "reproduce") as reproduce, \
             redirect_stdout(io.StringIO()) as output:
            self.assertEqual(r.main(), 0)
        preflight.assert_called_once()
        run.assert_not_called()
        reproduce.assert_not_called()
        self.assertIn("PREFLIGHT_ONLY", output.getvalue())
        self.assertNotIn('"status": "PASS"', output.getvalue())

    def test_wall_clock_budget_rejects_before_subprocess(self):
        r.DEADLINE = r.time.monotonic() - 1
        with mock.patch.object(subprocess, "run") as run, self.assertRaisesRegex(r.ReproductionError, "budget exceeded"):
            r.run(["lake", "--version"], self.repo)
        run.assert_not_called()

    def test_negative_raw_source_hash_is_not_a_manifest_or_status_flag(self):
        original = self.raw
        self.raw = original + b"\nchanged raw blob\n"
        with self.assertRaisesRegex(r.ReproductionError, "Raw source SHA-256 mismatch"):
            self.check_source()
        self.raw = original

    def test_main_cannot_hide_any_additional_command(self):
        target = self.lean / "Main.lean"
        data = target.read_text(encoding="utf-8")
        for extra in ("#eval 1", "set_option warningAsError false", "import Mathlib", "theorem hidden : True := by trivial"):
            target.write_text(data + "\n" + extra, encoding="utf-8")
            with self.subTest(extra=extra), self.assertRaisesRegex(r.ReproductionError, "Main must only import"):
                self.check_lean()
        target.write_text(data, encoding="utf-8")

    def test_dependency_tree_duplicate_and_unknown_git_modes_rejected(self):
        self.dependencies()
        for kind, mode in ((b"commit", b"160000"), (b"blob", b"120000"), (b"blob", b"100664")):
            record = mode + b" " + kind + b" " + b"0" * 40 + b"\tsource.lean\0"
            with self.subTest(mode=mode), self.assertRaises(r.ReproductionError):
                self.check_dependencies(lambda repo, args: record if args[0] == "ls-tree" else None)
        def duplicate(repo, args):
            return self.dependency_git(repo, *args) * 2 if args[0] == "ls-tree" else None
        with self.assertRaisesRegex(r.ReproductionError, "Duplicate dependency tree"):
            self.check_dependencies(duplicate)

    @unittest.skipUnless(os.name == "nt", "Windows inert-link exception only")
    def test_fixed_linktext_requires_exact_head_and_index_blob_even_with_clean_status(self):
        self.dependencies()
        relative = b"scripts/bench/build/fake-root/bin/lean.py"
        path = self.lean / ".lake" / "packages" / "mathlib" / relative.decode()
        path.parent.mkdir(parents=True)
        path.write_bytes(b"lean")
        exact_oid = r.WINDOWS_LINKTEXT["mathlib"][relative]
        for wrong_tree in (False, True):
            def changed(repo, args):
                if repo.name != "mathlib":
                    return None
                if args[0] == "ls-tree":
                    oid = b"0" * 40 if wrong_tree else exact_oid
                    return self.dependency_git(repo, *args) + b"120000 blob " + oid + b"\t" + relative + b"\0"
                if args[0] == "ls-files":
                    oid = exact_oid if wrong_tree else b"0" * 40
                    return self.dependency_git(repo, *args) + b"120000 " + oid + b" 0\t" + relative + b"\0"
                return None
            with self.subTest(wrong_tree=wrong_tree), self.assertRaisesRegex(r.ReproductionError, "inert-link.*blob mismatch"):
                self.check_dependencies(changed)

    def test_real_dependency_junction_cannot_be_a_checkout_or_untracked_cache(self):
        self.dependencies()
        outside = self.root / "dependency-outside"
        outside.mkdir()
        sentinel = outside / "keep"
        sentinel.write_bytes(b"outside remains")
        link = self.lean / ".lake" / "packages" / "mathlib" / "linked-cache"
        if os.name == "nt":
            result = subprocess.run(["cmd", "/c", "mklink", "/J", str(link), str(outside)],
                                    env=r.child_env(), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            self.assertEqual(result.returncode, 0)
        else:
            link.symlink_to(outside, target_is_directory=True)
        try:
            with self.assertRaisesRegex(r.ReproductionError, "Symlink/reparse path rejected"):
                self.check_dependencies()
            self.assertEqual(sentinel.read_bytes(), b"outside remains")
        finally:
            if os.name == "nt":
                os.rmdir(link)
            else:
                link.unlink()

    def test_missing_dependency_never_runs_lake_even_after_static_preflight(self):
        baseline = {"source": {}, "lock": r.expected_lock(), "theorems": {"names": self.names}, "files": {}}
        with mock.patch.object(r, "preflight", return_value=baseline), mock.patch.object(r, "run") as run, \
             mock.patch.object(r, "clean_project_build") as clean, \
             self.assertRaisesRegex(r.ReproductionError, "Missing physical dependency checkout"):
            r.reproduce(self.package, self.repo, "lake", True)
        run.assert_not_called()
        clean.assert_not_called()

    def test_scandir_fast_walk_resolves_directories_not_regular_files_including_caches(self):
        tree = self.root / "fast-tree"
        payloads = (tree / "source.lean", tree / ".lake" / "build" / "cache.bin",
                    tree / ".git" / "objects" / "object.bin")
        for path in payloads:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b"fixture")
        original = Path.resolve
        resolved = []
        def resolve(path, *args, **kwargs):
            resolved.append(path)
            self.assertNotIn(path, payloads, "Ordinary enumerated file should not resolve independently")
            return original(path, *args, **kwargs)
        checked = set()
        with mock.patch.object(Path, "resolve", resolve), redirect_stdout(io.StringIO()):
            files = r.audit_tree_entries(tree, checked)
        self.assertEqual(files, set(payloads))
        self.assertTrue(all(path.parent in checked for path in payloads))
        self.assertIn(tree / ".lake" / "build", resolved)
        self.assertIn(tree / ".git" / "objects", resolved)
        self.assertTrue(all(path not in checked for path in payloads), "Never memoize file state")

    def test_fast_walk_rejects_nonfollowing_file_reparse_metadata(self):
        tree = self.root / "fast-reparse"
        tree.mkdir()
        entry = SimpleNamespace(name="apparently-regular.bin",
                                stat=mock.Mock(return_value=SimpleNamespace(st_mode=stat.S_IFREG,
                                                                            st_file_attributes=0x400)))
        iterator = mock.MagicMock()
        iterator.__enter__.return_value = iter([entry])
        with mock.patch.object(os, "scandir", return_value=iterator), \
             self.assertRaisesRegex(r.ReproductionError, "Symlink/reparse"):
            r.audit_tree_entries(tree, set())
        entry.stat.assert_called_once_with(follow_symlinks=False)

    def test_tracked_fast_path_independently_lstats_after_walk(self):
        tree = self.root / "fresh-lstat"
        tree.mkdir()
        target = tree / "source.lean"
        target.write_bytes(b"initial")
        checked = set()
        with redirect_stdout(io.StringIO()):
            files = r.audit_tree_entries(tree, checked)
        original = Path.lstat
        seen = []
        def changed(path, *args, **kwargs):
            seen.append(path)
            if path == target:
                return SimpleNamespace(st_mode=stat.S_IFREG, st_file_attributes=0x400)
            return original(path, *args, **kwargs)
        with mock.patch.object(Path, "lstat", changed), self.assertRaisesRegex(r.ReproductionError, "Unsafe/missing"):
            r.tracked_file_path(tree, b"source.lean", files, checked)
        self.assertEqual(seen, [target])

    def test_fast_tracked_path_rejects_aliases_and_escapes_without_touching_sentinel(self):
        tree = self.root / "alias-tree"
        tree.mkdir()
        target = tree / "source.lean"
        target.write_bytes(b"fixture")
        sentinel = self.root / "outside-sentinel"
        sentinel.write_bytes(b"keep")
        checked = set()
        with redirect_stdout(io.StringIO()):
            files = r.audit_tree_entries(tree, checked)
        aliases = (b"../outside-sentinel", b"./source.lean", b"nested/../source.lean", b"nested//source.lean",
                   b"nested\\source.lean", b"/source.lean", b"SOURC~1.LEA", b"//server/share/source.lean")
        if os.name == "nt":
            aliases += (b"source.lean.", b"source.lean ", b"source.lean:stream", b"NUL", b"CON.lean")
        for alias in aliases:
            with self.subTest(alias=alias), self.assertRaises(r.ReproductionError):
                r.tracked_file_path(tree, alias, files, checked)
        self.assertEqual(sentinel.read_bytes(), b"keep")
        with self.assertRaisesRegex(r.ReproductionError, "alias"):
            r.safe_path(tree / ".." / "outside-sentinel", checked)

    def test_generic_path_canonical_alias_rejected_before_memoization(self):
        directory = self.root / "noncanonical"
        directory.mkdir()
        checked = set()
        with mock.patch.object(Path, "resolve", return_value=self.root / "outside"), \
             self.assertRaisesRegex(r.ReproductionError, "Path resolution changed"):
            r.safe_path(directory, checked)
        self.assertEqual(checked, set())

    def test_dependency_raw_bytes_changed_after_fast_walk_still_rejected(self):
        self.dependencies()
        original = r.audit_tree_entries
        def mutate(checkout, checked):
            files = original(checkout, checked)
            if checkout.name == "mathlib":
                (checkout / "source.lean").write_bytes(b"-- changed after enumeration\n")
            return files
        with mock.patch.object(r, "audit_tree_entries", side_effect=mutate), \
             self.assertRaisesRegex(r.ReproductionError, "bytes changed"):
            self.check_dependencies()

    def test_fresh_fast_scan_detects_real_junction_added_after_previous_pass(self):
        tree = self.root / "second-pass-tree"
        outside = self.root / "second-pass-outside"
        tree.mkdir()
        outside.mkdir()
        sentinel = outside / "keep"
        sentinel.write_bytes(b"preserved")
        with redirect_stdout(io.StringIO()):
            self.assertEqual(r.audit_tree_entries(tree, set()), set())
        link = tree / "injected"
        if os.name == "nt":
            result = subprocess.run(["cmd", "/c", "mklink", "/J", str(link), str(outside)],
                                    env=r.child_env(), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            self.assertEqual(result.returncode, 0)
        else:
            link.symlink_to(outside, target_is_directory=True)
        try:
            with self.assertRaisesRegex(r.ReproductionError, "Symlink/reparse"):
                r.audit_tree_entries(tree, set())
            self.assertEqual(sentinel.read_bytes(), b"preserved")
        finally:
            if os.name == "nt":
                os.rmdir(link)
            else:
                link.unlink()

    def test_profile_records_all_full_gates_and_keeps_failure_status(self):
        with mock.patch.object(r, "PROFILE_RECORDS", []):
            result, *_ = self.workflow()
        names = {entry["phase"] for entry in result["timings"]}
        self.assertTrue({"preflight.before", "dependencies.before", "preflight.before_cleanup",
                         "own_build.cleanup", "own_build.Main", "source.Check19", "preflight.after",
                         "dependencies.after"} <= names)
        self.assertTrue({"source.replay." + module for module in (*r.MODULES, "Main")} <= names)
        records = []
        with mock.patch.object(r, "PROFILE_RECORDS", records), redirect_stdout(io.StringIO()), \
             self.assertRaisesRegex(r.ReproductionError, "expected failure"):
            with r.phase("failed-stage"):
                raise r.ReproductionError("expected failure")
        self.assertEqual(records[0]["status"], "error")

    def workflow(self, changed=False, build_fails=False, skip_update=True):
        baseline = {"source": {}, "lock": r.expected_lock(), "theorems": {"names": self.names}, "files": {"manifest": "old"}}
        after = {**baseline, "files": {"manifest": "changed"}} if changed else baseline
        audit = "\n".join(n + " : True\n'" + n + "' does not depend on any axioms" for n in self.names).encode()
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
