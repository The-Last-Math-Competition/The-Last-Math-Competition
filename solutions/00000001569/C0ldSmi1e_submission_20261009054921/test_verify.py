#!/usr/bin/env python3
"""Negative controls for the portable verifier; optional compiled Lean controls.

python3 test_verify.py
python3 test_verify.py --compiled-controls --lake /path/to/lake
    --dependency-root /path/to/pinned/packages --output /new/control-results
"""
import argparse
import copy
import io
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

import verify

BASE = Path(__file__).resolve().parent


class VerifierControls(unittest.TestCase):
    def setUp(self):
        self.expected = verify.load_json(BASE / "verification/compiled-inventory.json")
        # Tests that mutate row zero must target a mathematical root, regardless of name ordering.
        self.expected.sort(key=lambda row: (row["unsafe"], row["name"]))
        self.actual = copy.deepcopy(self.expected)

    def reject(self):
        with self.assertRaises(ValueError):
            verify.validate_inventory(self.actual, self.expected)

    def test_reordering_preserves_meaning(self):
        self.actual.reverse()
        for row in self.actual:
            row["transitive_axioms"].reverse()
            row["direct_constants"].reverse()
        verify.validate_inventory(self.actual, self.expected)

    def test_sorry_axiom(self):
        self.actual[0]["transitive_axioms"].append("sorryAx")
        self.reject()

    def test_custom_transitive_axiom(self):
        self.actual[0]["transitive_axioms"].append("AssumedConclusion")
        self.reject()

    def test_authored_axiom(self):
        self.actual[0]["kind"] = "axiom"
        self.reject()

    def test_unsafe_declaration(self):
        self.actual[0]["unsafe"] = True
        self.reject()
        # A compiler-shaped name receives no wildcard exemption.
        for module in ["Solution"]:
            spoof = copy.deepcopy(self.expected[0])
            spoof.update(name="Spoof.match_1._cstage1", module=module,
                         unsafe=True, role="compiler_execution")
            with self.subTest(module=module), self.assertRaises(ValueError):
                verify.normalized_inventory(self.expected + [spoof])

    def test_false_like_unsafe_flag(self):
        self.actual[0]["unsafe"] = 0
        self.reject()

    def test_missing_generated_declaration(self):
        row = next((row for row in self.actual if "._proof_" in row["name"] or row["name"].startswith("_private.")), self.actual[0])
        self.actual.remove(row)
        self.reject()

    def test_extra_declaration(self):
        extra = copy.deepcopy(self.actual[0])
        extra["name"] = "OutsideExpectedNamespace.unreviewed"
        self.actual.append(extra)
        self.reject()

    def test_duplicate_replacing_declaration(self):
        self.actual[-1] = copy.deepcopy(self.actual[0])
        self.reject()

    def test_missing_mathematical_module(self):
        self.actual = []
        self.reject()

    def test_wrong_module(self):
        self.actual[0]["module"] = "Unreviewed"
        self.reject()

    def test_changed_type(self):
        self.actual[0]["type"] = "True"
        self.reject()
        self.actual = copy.deepcopy(self.expected)
        execution = next((r for r in self.actual if r["unsafe"]), None)
        if execution is not None:
            execution["type"] = "Nat"
            self.reject()

    def test_changed_direct_dependency(self):
        self.actual[0]["direct_constants"].append("Unreviewed.dependency")
        self.reject()
        # Even if a tampered expected inventory were supplied too, a safe root
        # cannot bridge through an owned helper to an unsafe execution node.
        self.actual = copy.deepcopy(self.expected)
        safe = [row for row in self.actual if not row["unsafe"]]
        if verify.COMPILER_ARTIFACTS and len(safe) >= 2:
            safe[0]["direct_constants"] = sorted(set(safe[0]["direct_constants"]) | {safe[1]["name"]})
            safe[1]["direct_constants"].append(sorted(verify.COMPILER_ARTIFACTS)[0])
            with self.assertRaisesRegex(ValueError, "Unsafe proof dependency"):
                verify.normalized_inventory(self.actual)
        self.actual = copy.deepcopy(self.expected)
        execution = next((r for r in self.actual if r["unsafe"]), None)
        if execution is not None:
            execution["direct_constants"].append("Unreviewed.dependency")
            self.reject()

    def test_duplicate_axiom_is_rejected_not_hidden(self):
        row = next(row for row in self.actual if row["transitive_axioms"])
        row["transitive_axioms"].append(row["transitive_axioms"][0])
        self.reject()

    def test_missing_type(self):
        del self.actual[0]["type"]
        self.reject()
        roots = sorted(r["name"] for r in self.expected if not r["unsafe"])
        closure = {"root_names": roots, "reachable_constant_names": roots.copy(),
                   "reachable_constant_count": len(roots), "unsafe_count": 0,
                   "axioms": [], "edge_sources": ["types", "values_including_theorem_proofs"]}
        verify.validate_closure(closure, self.expected)
        for field, value in [("root_names", roots[:-1]), ("unsafe_count", 1),
                             ("edge_sources", ["types"]), ("axioms", ["sorryAx"])]:
            broken = {**closure, field: value}
            with self.subTest(field=field), self.assertRaises(ValueError):
                verify.validate_closure(broken, self.expected)

    def test_forbidden_source_tokens(self):
        for token in ["sorry", "sorryAx", "admit", "axiom", "unsafe", "native_decide",
                      "implemented_by", "extern", "run_cmd", "elab", "macro", "initialize"]:
            with self.subTest(token=token), self.assertRaises(ValueError):
                verify.scan_source("def rejected := " + token)
        for name in ["Solution.lean"]:
            verify.scan_source((BASE / "lean" / name).read_text())

    def test_exact_dependency_manifest(self):
        pins = verify.load_json(BASE / "verification/pinned-dependencies.json")
        verify.validate_pins(pins, copy.deepcopy(pins))
        altered = copy.deepcopy(pins)
        altered["packages"][0]["rev"] = "0" * 40
        with self.assertRaises(ValueError):
            verify.validate_pins(pins, altered)
        altered = copy.deepcopy(pins)
        altered["packages"][-1] = copy.deepcopy(altered["packages"][0])
        with self.assertRaises(ValueError):
            verify.validate_pins(altered, altered)

    def test_frozen_source_tamper(self):
        with tempfile.TemporaryDirectory(prefix="tlmc1569-source-control-") as work:
            root = Path(work)
            for name in verify.INPUT_FILES:
                (root / name).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(BASE / name, root / name)
            manifest = verify.load_json(BASE / "verification/source-manifest.json")
            verify.validate_inputs(root, manifest)
            with (root / "lean/Solution.lean").open("a") as file:
                file.write("\n-- unexpected alteration\n")
            with self.assertRaisesRegex(ValueError, "Frozen input identity mismatch"):
                verify.validate_inputs(root, manifest)

    def test_frozen_inventory_file_tamper(self):
        with tempfile.TemporaryDirectory(prefix="tlmc1569-inventory-control-") as work:
            root = Path(work)
            for name in verify.INPUT_FILES:
                (root / name).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(BASE / name, root / name)
            manifest = verify.load_json(BASE / "verification/source-manifest.json")
            altered = copy.deepcopy(self.expected)
            altered[0]["type"] = "Changed"
            verify.write_json(root / "verification/compiled-inventory.json", altered)
            with self.assertRaisesRegex(ValueError, "Frozen input identity mismatch"):
                verify.validate_inputs(root, manifest)

    def test_manifest_cannot_rebaseline_frozen_math(self):
        with tempfile.TemporaryDirectory(prefix="tlmc1569-freeze-control-") as work:
            root = Path(work)
            for name in verify.INPUT_FILES:
                (root / name).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(BASE / name, root / name)
            manifest = verify.load_json(BASE / "verification/source-manifest.json")
            with (root / "lean/Solution.lean").open("a") as file:
                file.write("\n-- altered frozen mathematical source\n")
            manifest["source_sha256"]["lean/Solution.lean"] = verify.sha(root / "lean/Solution.lean")
            with self.assertRaisesRegex(ValueError, "Frozen mathematical source identity mismatch"):
                verify.validate_inputs(root, manifest)

    def test_lcProof_forbidden_in_mathematical_roots(self):
        next(r for r in self.actual if not r["unsafe"])["transitive_axioms"].append("lcProof")
        self.reject()

    def test_compiler_artifact_axiom_rejected(self):
        execution = next((r for r in self.actual if r["unsafe"]), None)
        if execution is None:
            self.skipTest("Frozen candidate has no compiler execution exceptions")
        execution["kind"] = "axiom"
        self.reject()

    def test_duplicate_json_keys(self):
        with tempfile.TemporaryDirectory(prefix="tlmc1569-json-control-") as work:
            p = Path(work) / "duplicate.json"
            p.write_text('{"key": 1, "key": 2}')
            with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
                verify.load_json(p)

    def test_failed_subprocess_record_is_preserved(self):
        with tempfile.TemporaryDirectory(prefix="tlmc1569-record-control-") as work:
            root = Path(work)
            recorder = verify.Recorder(root, root, os.environ.copy())
            with self.assertRaises(RuntimeError):
                recorder.run("intentional-failure", [sys.executable, "-I", "-c",
                             "import sys; print('actual output'); print('actual error', file=sys.stderr); sys.exit(7)"])
            record = verify.load_json(root / "intentional-failure/command.json")
            self.assertEqual(record["exit_code"], 7)
            self.assertEqual((root / "intentional-failure/stdout.txt").read_text(), "actual output\n")
            self.assertEqual((root / "intentional-failure/stderr.txt").read_text(), "actual error\n")

    def test_failed_launch_record_is_preserved(self):
        with tempfile.TemporaryDirectory(prefix="tlmc1569-launch-control-") as work:
            root = Path(work)
            recorder = verify.Recorder(root, root, os.environ.copy())
            with self.assertRaises(RuntimeError):
                recorder.run("missing-executable", [str(root / "absent")])
            record = verify.load_json(root / "missing-executable/command.json")
            self.assertIsNone(record["exit_code"])
            self.assertTrue(record["launch_error"])


def dependency_mutation_control(out, env):
    """Exercise real tracked-dirty detection in an isolated synthetic Git dependency.

    No supplied standard-library or user repository is mutated. The checker is
    the same check_pins function used against all nine real dependencies.
    """
    project = out / "dependency-mutation-fixture"
    repo = project / ".lake/packages/mathlib"
    repo.mkdir(parents=True)
    recorder = verify.Recorder(out, project, env)
    recorder.run("mutation-git-init", ["git", "-c", "init.templateDir=", "init", "-q", str(repo)])
    tracked = repo / "tracked-fixture.txt"
    original = b"clean dependency fixture\n"
    tracked.write_bytes(original)
    recorder.run("mutation-git-add", ["git", "-C", str(repo), "add", "tracked-fixture.txt"])
    recorder.run("mutation-git-commit", ["git", "-C", str(repo), "-c", "user.name=Verifier Fixture",
                 "-c", "user.email=verifier-fixture@example.invalid", "-c", "core.hooksPath=" + os.devnull,
                 "commit", "-q", "-m", "Temporary dependency mutation control"])
    revision = recorder.run("mutation-initial-head", ["git", "-C", str(repo), "rev-parse", "HEAD"]).strip()
    pin = [{"name": "mathlib", "rev": revision}]
    verify.check_pins("mutation-clean-before", pin, project, recorder)
    rejected = False
    diagnostic = ""
    try:
        tracked.write_bytes(b"deliberately altered tracked dependency fixture\n")
        try:
            verify.check_pins("mutation-dirty", pin, project, recorder)
        except ValueError as error:
            diagnostic = str(error)
            rejected = "Wrong revision or modified dependency: mathlib" in diagnostic
        current = recorder.run("mutation-unchanged-head", ["git", "-C", str(repo), "rev-parse", "HEAD"]).strip()
        if current != revision:
            raise RuntimeError("Mutation fixture unexpectedly changed revision")
        if not rejected:
            raise RuntimeError("Tracked dependency mutation was accepted")
    finally:
        tracked.write_bytes(original)
        verify.check_pins("mutation-clean-after", pin, project, recorder)
    result = {"result": "PASS", "expected_rejection": diagnostic,
              "unchanged_revision": revision, "restored_clean": True,
              "scope": "Isolated synthetic tracked Git dependency; shared checkouts untouched",
              "records": recorder.records}
    verify.write_json(out / "dependency-mutation-control.json", result)
    return result


def compiled_controls(args, out):
    pins = verify.validate_pins(verify.load_json(BASE / "verification/pinned-dependencies.json"),
                               verify.load_json(BASE / "lean/lake-manifest.json"))
    dependency_root = (args.dependency_root or BASE / "lean/.lake/packages").resolve(strict=True)
    fixtures = [
        ("custom-axiom", {"Solution": "axiom OutsideNamespace.assumed : False\n"}, "Authored axiom declaration"),
        ("unsafe-definition", {"Solution": "unsafe def OutsideNamespace.unchecked : Nat := 1\n"}, "Unsafe authored declaration"),
        ("compiler-name-spoof", {"Solution": "unsafe def Spoof.match_1._cstage1 : Nat := 1\n"}, "Unsafe authored declaration"),
        ("sorry-proof", {"Solution": "theorem OutsideNamespace.unsound : False := by sorry\n"}, "Forbidden transitive axiom sorryAx"),
        ("hidden-imported-proof-axiom", {
            "ImportedBridge": "axiom Hidden.assumption : False\ntheorem Hidden.intermediate : True := False.elim Hidden.assumption\n",
            "Solution": "import ImportedBridge\ntheorem Public.root : True := Hidden.intermediate\n"}, "Forbidden transitive axiom Hidden.assumption"),
        ("hidden-imported-type-axiom", {
            "ImportedBridge": "axiom Hidden.size : Nat\ndef Hidden.Index := Fin Hidden.size\n",
            "Solution": "import ImportedBridge\ntheorem Public.root (_ : Hidden.Index) : True := True.intro\n"}, "Forbidden transitive axiom Hidden.size"),
        ("hidden-imported-sorry-proof", {
            "ImportedBridge": "theorem Hidden.intermediate : False := by sorry\n",
            "Solution": "import ImportedBridge\ntheorem Public.root : True := False.elim Hidden.intermediate\n"}, "Forbidden transitive axiom sorryAx"),
    ]
    if verify.COMPILER_ARTIFACTS:
        allowed_name = sorted(verify.COMPILER_ARTIFACTS)[0]
        fixtures.append(("allowlisted-axiom-spoof",
            {"Solution": "unsafe axiom " + allowed_name + " : Nat\n"},
            "Authored axiom declaration"))
    # These two deliberately forged imported theorem fixtures bypass checking
    # only inside negative controls. They test the audit beyond ordinary Lean
    # elaboration: one uses an unsafe definition with no axioms, and one uses
    # the compiler-only lcProof axiom in an imported theorem proof value.
    fixtures.extend([
        ("hidden-imported-unsafe-proof", {"ImportedBridge": 'import Lean\nopen Lean Elab Command\nunsafe def Hidden.unsafeTrue : True := True.intro\nrun_cmd do\n  let decl : Declaration := .thmDecl {\n    name := `Hidden.safeBridge, levelParams := [], type := mkConst ``True,\n    value := mkConst `Hidden.unsafeTrue }\n  match (← getEnv).addDeclCore 0 decl none false with\n  | .ok env => setEnv env\n  | .error _ => throwError "fixture insertion failed"\n',
            "Solution": "import ImportedBridge\ntheorem Public.root : True := Hidden.safeBridge\n"}, "Unsafe proof dependency: Hidden.unsafeTrue"),
        ("hidden-imported-lcProof-proof", {"ImportedBridge": 'import Lean\nopen Lean Elab Command\nrun_cmd do\n  let decl : Declaration := .thmDecl {\n    name := `Hidden.safeBridge, levelParams := [], type := mkConst ``True,\n    value := mkApp (mkConst `lcProof) (mkConst ``True) }\n  match (← getEnv).addDeclCore 0 decl none false with\n  | .ok env => setEnv env\n  | .error _ => throwError "fixture insertion failed"\n',
            "Solution": "import ImportedBridge\ntheorem Public.root : True := Hidden.safeBridge\n"}, "Forbidden transitive axiom lcProof"),
    ])
    results = []
    pin_project = out / "dependency-check-project"
    (pin_project / ".lake/packages").mkdir(parents=True)
    for pin in pins:
        (pin_project / ".lake/packages" / pin["name"]).symlink_to(
            (dependency_root / pin["name"]).resolve(strict=True), target_is_directory=True)
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(("LEAN_", "LAKE_", "PYTHON")) and k != "ELAN_TOOLCHAIN"}
    env["GIT_OPTIONAL_LOCKS"] = "0"
    pin_recorder = verify.Recorder(out, pin_project, env)
    verify.check_pins("controls-before", pins, pin_project, pin_recorder)
    try:
        dependency_mutation_control(out, env)
        bad_pins = copy.deepcopy(pins)
        bad_pins[0]["rev"] = "0" * 40
        try:
            verify.check_pins("intentional-wrong-pin", bad_pins, pin_project, pin_recorder)
        except ValueError as error:
            if "Wrong revision" not in str(error):
                raise
            verify.write_json(out / "pin-tamper-control.json", {
                "result": "PASS", "expected_rejection": str(error),
                "note": "Expected revision changed only in memory; actual checkouts remain untouched."})
        else:
            raise RuntimeError("Wrong dependency revision was accepted")
        for label, modules, diagnostic in fixtures:
            dest = out / label
            project = dest / "fresh-project"
            (project / ".lake/packages").mkdir(parents=True)
            (project / "logs").mkdir()
            for name in ["lakefile.toml", "lake-manifest.json", "lean-toolchain", "Audit.lean"]:
                shutil.copyfile(BASE / "lean" / name, project / name)
            # Fixtures compile only their mathematical module and imported helpers;
            # the unmodified production audit is executed as a separate command.
            config = (project / "lakefile.toml").read_text().replace(
                'roots = ["Solution", "AuthorAudit", "Audit"]',
                'roots = ' + json.dumps(["Solution", "AuthorAudit"] + [m for m in modules if m != "Solution"]))
            (project / "lakefile.toml").write_text(config)
            (project / "AuthorAudit.lean").write_text("import Solution\n")
            for module, source in modules.items():
                (project / (module + ".lean")).write_text(source)
            for pin in pins:
                (project / ".lake/packages" / pin["name"]).symlink_to(
                    (dependency_root / pin["name"]).resolve(strict=True), target_is_directory=True)
            recorder = verify.Recorder(dest, project, env)
            recorder.run("compile-fixture", [args.lake, "build"])
            rejected = False
            try:
                recorder.run("audit-fixture", [args.lake, "env", "lean", "-DwarningAsError=true", "Audit.lean"])
            except RuntimeError:
                record = recorder.records[-1]
                rejected = record["exit_code"] != 0 and diagnostic in record["stdout"] + record["stderr"]
            if not rejected:
                raise RuntimeError("Compiled negative control did not produce expected rejection: " + label)
            if label == "sorry-proof":
                strict_rejected = False
                try:
                    recorder.run("strict-replay-fixture", [args.lake, "env", "lean",
                                                           "-DwarningAsError=true", "Solution.lean"])
                except RuntimeError:
                    record = recorder.records[-1]
                    strict_rejected = record["exit_code"] != 0 and "declaration uses 'sorry'" in record["stdout"] + record["stderr"]
                if not strict_rejected:
                    raise RuntimeError("Strict replay did not reject sorry fixture")
            result = {"control": label, "expected_rejection": diagnostic, "result": "PASS",
                      "fixture_modules": modules, "records": recorder.records}
            verify.write_json(dest / "result.json", result)
            results.append(result)
    finally:
        verify.check_pins("controls-after", pins, pin_project, pin_recorder)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiled-controls", action="store_true")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--dependency-root", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    out = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix="tlmc1569-controls-"))
    if args.output:
        out.mkdir(parents=True, exist_ok=False)
    frozen = verify.load_json(BASE / "verification/source-manifest.json")
    frozen_sha = verify.sha(BASE / "verification/source-manifest.json")
    input_hashes = verify.validate_inputs(BASE, frozen)
    stream = io.StringIO()
    result = unittest.TextTestRunner(stream=stream, verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(VerifierControls))
    (out / "unit-tests.txt").write_text(stream.getvalue())
    print(stream.getvalue())
    report = {"result": "FAIL", "unit_test_count": result.testsRun, "unit_tests_pass": result.wasSuccessful(),
              "unit_test_skipped_count": len(result.skipped),
              "unit_test_skipped": [{"test": str(test), "reason": reason} for test, reason in result.skipped],
              "compiled_controls": [], "errors": []}
    try:
        if not result.wasSuccessful():
            raise RuntimeError("Unit controls failed")
        if args.compiled_controls:
            report["compiled_controls"] = compiled_controls(args, out)
            report["dependency_mutation_control"] = verify.load_json(out / "dependency-mutation-control.json")
            report["revision_mismatch_control"] = verify.load_json(out / "pin-tamper-control.json")
        verify.validate_inputs(BASE, frozen)
        if verify.sha(BASE / "verification/source-manifest.json") != frozen_sha:
            raise ValueError("Control input manifest changed during execution")
        report.update(result="PASS", input_sha256=input_hashes, inputs_unchanged=True,
                      pins_clean_before_and_after=bool(args.compiled_controls))
    except Exception as error:
        report["errors"].append(type(error).__name__ + ": " + str(error))
    verify.write_json(out / "result.json", report)
    verify.write_json(out / "SHA256SUMS.json", {
        str(p.relative_to(out)): verify.sha(p) for p in out.rglob("*")
        if p.is_file() and ".lake" not in p.relative_to(out).parts and p.name != "SHA256SUMS.json"})
    print(report["result"] + ": negative controls; records: " + str(out))
    return 0 if report["result"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
