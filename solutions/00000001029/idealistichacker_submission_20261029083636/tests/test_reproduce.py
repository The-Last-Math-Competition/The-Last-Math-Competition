"""Offline reproducer safety regressions: mocked tools, tiny owned fixtures, no Lean."""
from __future__ import annotations

from contextlib import redirect_stdout
import hashlib
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
AUDIT = Path(os.environ.get("TLMC1029_TEST_AUDIT_DIR",
                            str(Path(tempfile.gettempdir()) / "tlmc1029-reproducer-tests"))).absolute()
REPRODUCER_BYTES = (PACKAGE / "reproduce.py").read_bytes()
REPRODUCER_SHA256 = hashlib.sha256(REPRODUCER_BYTES).hexdigest()
SPEC = importlib.util.spec_from_file_location("tlmc1029_reproducer_tested", PACKAGE / "reproduce.py")
assert SPEC is not None
r = importlib.util.module_from_spec(SPEC)
exec(compile(REPRODUCER_BYTES, str(PACKAGE / "reproduce.py"), "exec"), r.__dict__)


class ReproducerSafetyTests(unittest.TestCase):
    def setUp(self):
        AUDIT.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="case-", dir=AUDIT)
        self.root = Path(self.temp.name).resolve()
        self.addCleanup(self.clean_fixture)
        self.package = self.root / "package"
        self.lean = self.package / "lean4"
        self.lean.mkdir(parents=True)
        # Explicit author-only copies: never enumerate or copy .lake/cache contents.
        files = [m + ".lean" for m in r.MODULES]
        files += ["Check.lean", "CheckDefinitions.lean", "lakefile.lean", "lean-toolchain", "lake-manifest.json"]
        for name in files:
            shutil.copyfile(PACKAGE / "lean4" / name, self.lean / name)
        for name in ("source.md", "submission.json"):
            shutil.copyfile(PACKAGE / name, self.package / name)
        self.manifest = json.loads((self.package / "submission.json").read_text(encoding="utf-8"))
        self.names = list(r.THEOREMS)
        self.raw = (self.package / "source.md").read_bytes()
        self.repo = self.root / "repo"
        (self.repo / "conjectures").mkdir(parents=True)
        self.current = self.repo / "conjectures" / (r.CID + ".md")
        self.current.write_bytes(self.raw)
        self.addCleanup(setattr, r, "DEADLINE", r.DEADLINE)
        self.addCleanup(setattr, r, "LAKE_BIN", r.LAKE_BIN)
        r.DEADLINE = None
        for owner, name in ((r, "git"), (r.subprocess, "Popen"), (r.subprocess, "run")):
            patch = mock.patch.object(owner, name, side_effect=AssertionError("Real tool forbidden in unit fixture"))
            patch.start()
            self.addCleanup(patch.stop)
        patch = mock.patch.object(r.os, "killpg", create=True, side_effect=AssertionError("Real process kill forbidden"))
        patch.start()
        self.addCleanup(patch.stop)

    def clean_fixture(self):
        resolved = Path(self.temp.name).resolve()
        boundary = AUDIT.resolve()
        if resolved == boundary or not resolved.is_relative_to(boundary) or not resolved.name.startswith("case-"):
            raise AssertionError("Refuse fixture cleanup outside the created audit boundary")
        self.temp.cleanup()

    def edit(self, name, transform):
        path = self.lean / name
        path.write_text(transform(path.read_text(encoding="utf-8")), encoding="utf-8", newline="\n")

    def source_git(self, repo, *args):
        self.assertEqual(repo, self.repo)
        return {("cat-file", "-t", r.SOURCE_COMMIT): b"commit\n",
                ("rev-parse", r.SOURCE_COMMIT + ":conjectures/" + r.CID + ".md"): r.SOURCE_BLOB.encode(),
                ("cat-file", "-t", r.SOURCE_BLOB): b"blob\n",
                ("cat-file", "blob", r.SOURCE_BLOB): self.raw}[args]

    def check_source(self, override=None, manifest=None):
        def answer(repo, *args):
            value = override(args) if override else None
            return self.source_git(repo, *args) if value is None else value
        with mock.patch.object(r, "git", side_effect=answer):
            return r.validate_source(self.package, self.repo, manifest or self.manifest)

    def check_lean(self):
        return r.validate_lean(self.lean, self.names)

    def make_dependencies(self):
        for spec in r.expected_lock()["packages"]:
            checkout = self.lean / ".lake/packages" / spec["name"]
            (checkout / ".git").mkdir(parents=True)
            (checkout / "source.lean").write_bytes(b"-- fixture\n")

    def dependency_git(self, repo, *args):
        self.assertTrue(repo.is_relative_to(self.root))
        spec = next(p for p in r.expected_lock()["packages"] if p["name"] == repo.name)
        data = b"-- fixture\n"
        oid = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest().encode()
        return {("rev-parse", "--show-toplevel"): str(repo).encode(),
                ("rev-parse", "--absolute-git-dir"): str(repo / ".git").encode(),
                ("rev-parse", "HEAD"): spec["rev"].encode(),
                ("remote", "get-url", "origin"): spec["url"].encode(),
                ("status", "--porcelain=v1", "-z", "--untracked-files=no", "--ignore-submodules=none"): b"",
                ("ls-files", "--stage", "-z"): b"100644 " + oid + b" 0\tsource.lean\0",
                ("ls-tree", "-r", "-z", "--full-tree", "HEAD"): b"100644 blob " + oid + b"\tsource.lean\0"}[args]

    def check_dependencies(self, override=None):
        def answer(repo, *args):
            value = override(repo, args) if override else None
            return self.dependency_git(repo, *args) if value is None else value
        with mock.patch.object(r, "git", side_effect=answer), redirect_stdout(io.StringIO()):
            return r.materialized_dependencies(self.lean, r.expected_lock())

    def type_output(self, names=None, prefix=""):
        return "\n".join(prefix + n + ".{u_1} {K : Type u_1} :\n  True\n'" + n +
                         "' depends on axioms: [propext, Quot.sound]" for n in (names or self.names))

    def runtime_fixture(self):
        lake = self.root / "toolchain/bin/lake.exe"
        paths = [self.lean / ".lake/build/lib/lean", lake.parent.parent / "lib/lean"]
        paths += [self.lean / ".lake/packages" / n / ".lake/build/lib/lean" for n, *_ in r.DEPENDENCIES]
        values = dict.fromkeys(r.RUNTIME_KEYS)
        values.update(PATH=str(lake.parent), LEAN_PATH=os.pathsep.join(map(str, paths)),
                      LEAN_SYSROOT=str(lake.parent.parent))
        return lake, values

    def runtime(self, mutate=None):
        lake, values = self.runtime_fixture()
        if mutate:
            mutate(values)
        with mock.patch.object(r, "run", return_value=json.dumps(values).encode()) as run:
            result = r.runtime_environment(self.lean, lake)
        self.assertEqual(run.call_args.args[0][:3], [str(lake), "--offline", "env"])
        return result

    def test_real_122_theorem_and_50_definition_inventory(self):
        self.assertFalse((self.lean / ".lake").exists())
        self.assertEqual(r.theorem_names(self.manifest), self.names)
        result = self.check_lean()
        self.assertEqual(result["count"], 122)
        self.assertEqual(len(set(result["names"])), 122)
        self.assertEqual(len(result["definitions"]), 50)

    def test_frozen_math_source_hash_tamper_rejected(self):
        self.edit("CarrierCodes.lean", lambda s: s + "\n-- raw byte mutation\n")
        with self.assertRaisesRegex(r.ReproductionError, "raw hash"):
            self.check_lean()

    def test_declaration_tamper_even_if_fixture_hash_rebound_rejected(self):
        self.edit("CarrierCodes.lean", lambda s: s.replace("theorem mem_allCarriers", "theorem renamedCarrier", 1))
        rebound = dict(r.MATH_HASHES, CarrierCodes=r.sha256((self.lean / "CarrierCodes.lean").read_bytes()))
        with mock.patch.object(r, "MATH_HASHES", rebound), self.assertRaisesRegex(r.ReproductionError, "inventory"):
            self.check_lean()

    def test_extra_lean_module_at_root_or_nested_rejected(self):
        for relative in ("Injected.lean", "nested/Injected.lean"):
            target = self.lean / relative
            target.parent.mkdir(exist_ok=True)
            target.write_text("theorem injected : True := by trivial\n", encoding="utf-8")
            with self.subTest(relative=relative), self.assertRaises(r.ReproductionError):
                self.check_lean()
            target.unlink()

    def test_check_extra_commands_rejected(self):
        target = self.lean / "Check.lean"
        original = target.read_bytes()
        for command in ("#eval 1", "#check True", "#print prefix Steiner1029", "set_option warningAsError false",
                        "#print axioms " + self.names[0], "import Mathlib"):
            target.write_bytes(original + command.encode() + b"\n")
            with self.subTest(command=command), self.assertRaises(r.ReproductionError):
                self.check_lean()
        target.write_bytes(original)

    def test_check_missing_or_reordered_query_rejected(self):
        original = (self.lean / "Check.lean").read_text(encoding="utf-8")
        for text in (original.replace("#check " + self.names[0] + "\n", "", 1),
                     original.replace(self.names[0], "Steiner1029.unadvertised", 1)):
            (self.lean / "Check.lean").write_text(text, encoding="utf-8", newline="\n")
            with self.assertRaises(r.ReproductionError):
                self.check_lean()

    def test_definition_check_extra_command_rejected(self):
        self.edit("CheckDefinitions.lean", lambda s: s + "#check True\n")
        with self.assertRaises(r.ReproductionError):
            self.check_lean()

    def test_manifest_missing_duplicate_extra_theorem_rejected(self):
        for names in (self.names[:-1], self.names + [self.names[0]], self.names[:-1] + ["Steiner1029.fake"]):
            manifest = dict(self.manifest, theorems=names)
            with self.subTest(count=len(names)), self.assertRaises(r.ReproductionError):
                r.theorem_names(manifest)

    def test_manifest_definition_inventory_tamper_rejected(self):
        for names in (list(r.DEFINITIONS)[:-1], list(r.DEFINITIONS) + [r.DEFINITIONS[0]], []):
            with self.assertRaises(r.ReproductionError):
                r.theorem_names(dict(self.manifest, audited_definitions=names))

    def test_config_lock_all_nine_and_alternate_lakefile_rejected(self):
        self.assertEqual(r.validate_config(self.lean), r.expected_lock())
        for index in range(9):
            lock = r.expected_lock()
            lock["packages"][index]["rev"] = "0" * 40
            (self.lean / "lake-manifest.json").write_text(json.dumps(lock), encoding="utf-8")
            with self.subTest(index=index), self.assertRaises(r.ReproductionError):
                r.validate_config(self.lean)
        (self.lean / "lake-manifest.json").write_text(json.dumps(r.expected_lock()), encoding="utf-8")
        (self.lean / "lakefile.toml").write_text("", encoding="utf-8")
        with self.assertRaises(r.ReproductionError):
            r.validate_config(self.lean)

    def test_source_real_raw_blob_and_current_crlf_bridge(self):
        self.current.write_bytes(self.raw.replace(b"\n", b"\r\n"))
        self.assertEqual(self.check_source()["blob"], r.SOURCE_BLOB)

    def test_source_manifest_identity_tamper_rejected(self):
        for key in ("source_commit", "source_git_blob", "source_sha256"):
            with self.subTest(key=key), self.assertRaises(r.ReproductionError):
                self.check_source(manifest=dict(self.manifest, **{key: "0" * 64}))

    def test_source_commit_type_blob_type_or_tree_binding_rejected(self):
        for command, wrong in ((("cat-file", "-t", r.SOURCE_COMMIT), b"blob"),
                               (("cat-file", "-t", r.SOURCE_BLOB), b"commit"),
                               (("rev-parse", r.SOURCE_COMMIT + ":conjectures/" + r.CID + ".md"), b"0" * 40)):
            with self.subTest(command=command), self.assertRaises(r.ReproductionError):
                self.check_source(lambda args: wrong if args == command else None)

    def test_source_raw_sha_and_blob_hash_both_enforced(self):
        changed = self.raw + b"changed\n"
        with self.assertRaisesRegex(r.ReproductionError, "SHA-256"):
            self.check_source(lambda args: changed if args == ("cat-file", "blob", r.SOURCE_BLOB) else None)
        with mock.patch.object(r, "SOURCE_SHA256", r.sha256(changed)), self.assertRaisesRegex(r.ReproductionError, "Git-blob"):
            self.check_source(lambda args: changed if args == ("cat-file", "blob", r.SOURCE_BLOB) else None,
                              dict(self.manifest, source_sha256=r.sha256(changed)))

    def test_current_english_and_chinese_mutations_rejected(self):
        text = self.raw.decode("utf-8")
        for changed in (text.replace("Conjecture", "Altered", 1), text.replace("\u731c\u60f3", "\u8bf4\u6cd5", 1)):
            self.assertNotEqual(text, changed)
            self.current.write_text(changed, encoding="utf-8", newline="\n")
            with self.assertRaises(r.ReproductionError):
                self.check_source()

    def test_frozen_source_crlf_or_extra_bytes_rejected(self):
        for data in (self.raw.replace(b"\n", b"\r\n"), self.raw + b"\n"):
            (self.package / "source.md").write_bytes(data)
            with self.assertRaises(r.ReproductionError):
                self.check_source()

    def test_actual_types_all_122_and_at_prefix_are_accepted(self):
        self.assertEqual(set(r.audit_theorem_types(self.type_output(), self.names)), set(self.names))
        self.assertEqual(set(r.audit_theorem_types(self.type_output(prefix="@"), self.names)), set(self.names))

    def test_actual_types_missing_duplicate_extra_or_unindented_rejected(self):
        valid = self.type_output()
        for invalid in (self.type_output(self.names[:-1]), valid + "\n" + self.type_output(self.names[:1]),
                        valid + "\nextra diagnostic", valid.replace("  True", "extra diagnostic", 1),
                        valid.replace(self.names[0] + ".{u_1}", "Steiner1029.fake", 1)):
            with self.assertRaises(r.ReproductionError):
                r.audit_theorem_types(invalid, self.names)

    def test_axioms_standard_and_empty_are_accepted(self):
        self.assertEqual(len(r.audit_axioms(self.type_output(), self.names)), 122)
        one = self.names[0]
        self.assertEqual(r.audit_axioms("'" + one + "' does not depend on any axioms", [one]), {one: []})

    def test_axioms_nonstandard_duplicate_missing_and_unknown_rejected(self):
        valid = self.type_output()
        for invalid in (valid.replace("Quot.sound", "sorryAx", 1), valid.replace("Quot.sound", "Custom.axiom", 1),
                        valid + "\n" + self.type_output(self.names[:1]), self.type_output(self.names[:-1]),
                        valid + "\n'Steiner1029.unknown' does not depend on any axioms"):
            with self.assertRaises(r.ReproductionError):
                r.audit_axioms(invalid, self.names)

    def test_child_env_strips_credentials_git_lean_lake_pollution(self):
        dirty = {k: "sentinel" for k in ("Gh_ToKeN", "GITHUB_TOKEN", "CUSTOM_SECRET", "PASSWORD", "MY_AUTH",
                  "COOKIE", "SSH_AUTH_SOCK", "GIT_DIR", "GIT_CONFIG_KEY_99", "LEAN_PATH", "LEAN_SYSROOT",
                  "LEAN_SRC_PATH", "LAKE_HOME", "AWS_ACCESS_KEY_ID", "OPENAI_API_KEY")}
        dirty.update(PATH="kept-path", OK="kept")
        with mock.patch.dict(os.environ, dirty, clear=True):
            env = r.child_env()
        self.assertNotIn("sentinel", env.values())
        self.assertEqual(env["OK"], "kept")
        self.assertEqual(env["GIT_CONFIG_COUNT"], "2")
        self.assertEqual(env["GIT_CONFIG_VALUE_0"], "")
        self.assertEqual(env["MATHLIB_NO_CACHE_ON_UPDATE"], "1")

    def test_safe_path_dot_aliases_rejected(self):
        with self.assertRaises(r.ReproductionError):
            r.safe_path(self.root / "child/../alias")

    def test_windows_device_ads_trailing_aliases_rejected(self):
        for name in ("NUL", "con.txt", "COM1", "LPT9.log", "a:stream", "tail.", "tail "):
            with mock.patch.object(r.os, "name", "nt"), self.subTest(name=name), self.assertRaises(r.ReproductionError):
                r.lexical_component(name)

    def test_drive_relative_path_is_rejected(self):
        if self.root.drive:
            alias = Path(self.root.drive + "relative-test-boundary")
            with self.assertRaises(r.ReproductionError):
                r.safe_path(alias)
        else:
            # Exercise Windows lexical semantics without depending on a host drive.
            with mock.patch.object(r.os, "name", "nt"), self.assertRaises(r.ReproductionError):
                r.lexical_component("C:relative-test-boundary")

    def test_cleanup_only_exact_build_and_no_neighbors(self):
        build = self.lean / ".lake/build"
        build.mkdir(parents=True)
        (build / "generated").write_bytes(b"owned")
        neighbor = self.lean / ".lake/packages"
        neighbor.mkdir()
        sentinel = neighbor / "keep"
        sentinel.write_bytes(b"keep")
        for target in (neighbor, self.root, self.lean / ".lake/build/../build"):
            with self.subTest(target=target), self.assertRaises(r.ReproductionError):
                r.clean_project_build(self.lean, target)
        r.clean_project_build(self.lean)
        self.assertFalse(build.exists())
        self.assertEqual(sentinel.read_bytes(), b"keep")

    def test_cleanup_missing_is_noop_and_file_is_rejected(self):
        r.clean_project_build(self.lean)
        build = self.lean / ".lake/build"
        build.parent.mkdir(exist_ok=True)
        build.write_bytes(b"not directory")
        with self.assertRaises(r.ReproductionError):
            r.clean_project_build(self.lean)
        self.assertEqual(build.read_bytes(), b"not directory")

    def test_cleanup_simulated_reparse_ancestors_and_descendant_rejected(self):
        nested = self.lean / ".lake/build/nested"
        nested.mkdir(parents=True)
        sentinel = nested / "keep"
        sentinel.write_bytes(b"keep")
        original = Path.lstat
        for rejected in (self.lean / ".lake", nested.parent, nested):
            def inspect(path, *args, **kwargs):
                if path == rejected:
                    return SimpleNamespace(st_mode=stat.S_IFDIR, st_file_attributes=1024)
                return original(path, *args, **kwargs)
            with mock.patch.object(Path, "lstat", inspect), self.subTest(path=rejected), self.assertRaises(r.ReproductionError):
                r.clean_project_build(self.lean)
            self.assertEqual(sentinel.read_bytes(), b"keep")

    def test_nine_physical_mock_git_checkouts_pass(self):
        self.make_dependencies()
        self.assertEqual(len(self.check_dependencies()), 9)

    def test_reparse_file_in_build_cannot_trigger_recursive_cleanup(self):
        build = self.lean / ".lake/build"
        build.mkdir(parents=True)
        outside = self.root / "outside-sentinel"
        outside.write_bytes(b"keep")
        entry = SimpleNamespace(name="alias", stat=lambda **kwargs:
                                SimpleNamespace(st_mode=stat.S_IFREG, st_file_attributes=1024))
        listing = mock.MagicMock()
        listing.__enter__.return_value = iter([entry])
        with mock.patch.object(r.os, "scandir", return_value=listing), \
                mock.patch.object(r.shutil, "rmtree") as delete, self.assertRaises(r.ReproductionError):
            r.clean_project_build(self.lean)
        delete.assert_not_called()
        self.assertEqual(outside.read_bytes(), b"keep")

    def test_missing_or_redirecting_dotgit_rejected_without_git(self):
        self.make_dependencies()
        dotgit = self.lean / ".lake/packages/mathlib/.git"
        dotgit.rmdir()
        with mock.patch.object(r, "git") as git, self.assertRaises(r.ReproductionError):
            r.materialized_dependencies(self.lean, r.expected_lock())
        git.assert_not_called()
        dotgit.write_text("gitdir: ../../outside\n", encoding="utf-8")
        with self.assertRaises(r.ReproductionError):
            self.check_dependencies()

    def test_dependency_origin_head_parent_metadata_dirty_rejected(self):
        self.make_dependencies()
        for command, wrong in ((("rev-parse", "HEAD"), b"0" * 40),
                               (("remote", "get-url", "origin"), b"https://example.invalid/wrong"),
                               (("rev-parse", "--show-toplevel"), str(self.lean).encode()),
                               (("rev-parse", "--absolute-git-dir"), str(self.root).encode()),
                               (("status", "--porcelain=v1", "-z", "--untracked-files=no", "--ignore-submodules=none"), b" M source.lean\0")):
            with self.subTest(command=command), self.assertRaises(r.ReproductionError):
                self.check_dependencies(lambda repo, args: wrong if args == command else None)

    def test_tracked_raw_tamper_despite_clean_status_rejected(self):
        self.make_dependencies()
        path = self.lean / ".lake/packages/mathlib/source.lean"
        path.write_bytes(b"-- changed despite clean git status\n")
        with self.assertRaisesRegex(r.ReproductionError, "bytes changed"):
            self.check_dependencies()
        path.write_bytes(b"-- fixture\r\n")
        self.assertEqual(len(self.check_dependencies()), 9)

    def test_dependency_index_tree_difference_and_duplicate_rejected(self):
        self.make_dependencies()
        for which in ("ls-tree", "ls-files"):
            with self.subTest(which=which), self.assertRaises(r.ReproductionError):
                self.check_dependencies(lambda repo, args: self.dependency_git(repo, *args) * 2 if args[0] == which else None)
        with self.assertRaisesRegex(r.ReproductionError, "index differs"):
            self.check_dependencies(lambda repo, args: b"" if args[0] == "ls-tree" else None)

    def test_gitlinks_unknown_symlinks_unmerged_and_traversal_rejected(self):
        self.make_dependencies()
        for record in (b"160000 a 0\tsource.lean\0", b"120000 a 0\tsource.lean\0",
                       b"100644 a 1\tsource.lean\0", b"100644 a 0\t../../source.md\0"):
            with self.subTest(record=record), self.assertRaises(r.ReproductionError):
                self.check_dependencies(lambda repo, args: record if args[0] == "ls-files" else None)

    def test_all_three_fixed_inert_links_exact_bytes_and_oids(self):
        self.make_dependencies()
        self.assertEqual(sum(map(len, r.WINDOWS_LINKTEXT.values())), 3)
        contents = {("mathlib", b"scripts/bench/build/fake-root/bin/lean.py"): b"lean",
                    ("mathlib", b"scripts/bench/size/run.py"): b"run",
                    ("batteries", b"docs/README.md"): b"../README.md"}
        for (name, relative), data in contents.items():
            path = self.lean / ".lake/packages" / name / relative.decode()
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        def extras(repo, args):
            entries = r.WINDOWS_LINKTEXT.get(repo.name, {})
            if args[0] == "ls-files":
                return self.dependency_git(repo, *args) + b"".join(b"120000 " + oid + b" 0\t" + rel + b"\0" for rel, oid in entries.items())
            if args[0] == "ls-tree":
                return self.dependency_git(repo, *args) + b"".join(b"120000 blob " + oid + b"\t" + rel + b"\0" for rel, oid in entries.items())
            return None
        if os.name == "nt":
            self.assertEqual(len(self.check_dependencies(extras)), 9)
        else:
            with self.assertRaises(r.ReproductionError):
                self.check_dependencies(extras)
        for (name, relative), original in contents.items():
            path = self.lean / ".lake/packages" / name / relative.decode()
            path.write_bytes(b"polluted")
            with self.subTest(path=relative), self.assertRaises(r.ReproductionError):
                self.check_dependencies(extras)
            path.write_bytes(original)
        self.assertFalse(r.dependency_mode_allowed("mathlib", b"120000", b"Mathlib/Injected.lean"))
        self.assertFalse(r.dependency_mode_allowed("aesop", b"120000", b"docs/README.md"))

    def test_runtime_exact_eleven_dirs_and_sysroot(self):
        env = self.runtime()
        self.assertEqual(len(set(env["LEAN_PATH"].split(os.pathsep))), 11)

    def test_all_fixed_inert_link_tree_oids_are_pinned(self):
        self.make_dependencies()
        for name, entries in r.WINDOWS_LINKTEXT.items():
            for relative in entries:
                path = self.lean / ".lake/packages" / name / relative.decode()
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(b"fixture placeholder")
                def wrong(repo, args):
                    if repo.name == name and args[0] == "ls-tree":
                        return self.dependency_git(repo, *args) + b"120000 blob " + b"0" * 40 + b"\t" + relative + b"\0"
                    return None
                with self.subTest(name=name, path=relative), self.assertRaises(r.ReproductionError):
                    self.check_dependencies(wrong)

    def test_runtime_old_olean_external_missing_empty_and_sysroot_rejected(self):
        lake, baseline = self.runtime_fixture()
        bad_paths = (baseline["LEAN_PATH"] + os.pathsep + str(self.root / "old-author-olean"),
                     os.pathsep.join(baseline["LEAN_PATH"].split(os.pathsep)[:-1]),
                     baseline["LEAN_PATH"] + os.pathsep)
        for paths in bad_paths:
            with self.subTest(paths=paths), self.assertRaises(r.ReproductionError):
                self.runtime(lambda values: values.update(LEAN_PATH=paths))
        with self.assertRaises(r.ReproductionError):
            self.runtime(lambda values: values.update(LEAN_SYSROOT=str(self.root / "wrong-sysroot")))

    def test_runtime_unknown_key_bad_type_and_missing_key_rejected(self):
        for mutate in (lambda v: v.update(INJECTED="yes"), lambda v: v.update(LEAN_PATH=12), lambda v: v.pop("PATH")):
            with self.assertRaises(r.ReproductionError):
                self.runtime(mutate)

    def test_run_success_uses_mock_popen_and_exact_stdout(self):
        process = mock.Mock(returncode=0)
        process.communicate.return_value = (b"raw\r\n", b"diagnostic")
        with mock.patch.object(r.subprocess, "Popen", return_value=process) as popen:
            self.assertEqual(r.run(["mock-tool"], self.repo), b"raw\r\n")
        self.assertEqual(popen.call_args.kwargs["stdin"], subprocess.DEVNULL)
        self.assertEqual(popen.call_args.kwargs["creationflags"] if os.name == "nt" else
                         popen.call_args.kwargs["start_new_session"],
                         subprocess.CREATE_NEW_PROCESS_GROUP if os.name == "nt" else True)

    def test_run_timeout_only_mock_owned_tree_and_fallback_kill(self):
        process = mock.Mock(pid=77331, returncode=-9)
        process.poll.return_value = None
        process.communicate.side_effect = [subprocess.TimeoutExpired(["mock-tool"], 0.01), (b"partial", b"")]
        with mock.patch.object(r.subprocess, "Popen", return_value=process), \
                mock.patch.object(r.subprocess, "run") as taskkill, \
                mock.patch.object(r.os, "killpg", create=True) as killpg, redirect_stdout(io.StringIO()):
            with self.assertRaisesRegex(r.ReproductionError, "owned process tree"):
                r.run(["mock-tool"], self.repo, timeout=0.01)
        if os.name == "nt":
            self.assertEqual(taskkill.call_args.args[0], ["taskkill.exe", "/PID", "77331", "/T", "/F"])
            killpg.assert_not_called()
        else:
            killpg.assert_called_once_with(77331, r.signal.SIGKILL)
            taskkill.assert_not_called()
        process.kill.assert_called_once()
        self.assertEqual(process.communicate.call_args.kwargs["timeout"], 15)

    def test_run_expired_deadline_or_spawn_error_does_not_kill(self):
        r.DEADLINE = r.time.monotonic() - 1
        with mock.patch.object(r.subprocess, "Popen") as popen, self.assertRaises(r.ReproductionError):
            r.run(["mock-tool"], self.repo)
        popen.assert_not_called()
        r.DEADLINE = None
        with mock.patch.object(r.subprocess, "Popen", side_effect=OSError("fixture")), \
                mock.patch.object(r.subprocess, "run") as kill, self.assertRaises(r.ReproductionError):
            r.run(["mock-tool"], self.repo)
        kill.assert_not_called()

    def test_timeout_of_already_finished_process_never_kills(self):
        process = mock.Mock(pid=77331, returncode=0)
        process.poll.return_value = 0
        process.communicate.side_effect = subprocess.TimeoutExpired(["mock-tool"], 0.01)
        with mock.patch.object(r.subprocess, "Popen", return_value=process), \
                mock.patch.object(r.subprocess, "run") as taskkill, \
                mock.patch.object(r.os, "killpg", create=True) as killpg, self.assertRaises(r.ReproductionError):
            r.run(["mock-tool"], self.repo, timeout=0.01)
        taskkill.assert_not_called()
        killpg.assert_not_called()
        process.kill.assert_not_called()

    def test_frozen_files_detects_author_changes_but_ignores_own_cache(self):
        before = r.frozen_files(self.package)
        cache = self.lean / ".lake/build"
        cache.mkdir(parents=True)
        (cache / "generated.olean").write_bytes(b"cache")
        self.assertEqual(r.frozen_files(self.package), before)
        (self.package / "author.txt").write_bytes(b"new authored file")
        self.assertNotEqual(r.frozen_files(self.package), before)


if __name__ == "__main__":
    unittest.main()
