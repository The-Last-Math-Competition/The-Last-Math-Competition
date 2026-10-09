#!/usr/bin/env python3
"""Adversarial verifier tests, including real Lean compilation and audit fixtures."""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
import verify

LEAN = None


def encode(records):
    return "\n".join(verify.PREFIX + json.dumps(record, separators=(",", ":")) for record in records) + "\n"


def records():
    return [
        {"event": "begin", "modules": ["Fixture"]},
        {"event": "declaration", "name": "Fixture.helper", "module": "Fixture", "kind": "theorem", "unsafe": False, "axioms": []},
        {"event": "declaration", "name": "Fixture.result", "module": "Fixture", "kind": "theorem", "unsafe": False, "axioms": ["propext"]},
        {"event": "closure", "names": ["Fixture.helper", "Fixture.result", "True", "True.intro", "propext"]},
        {"event": "end", "count": 2},
    ]


class ParserAndPolicyTests(unittest.TestCase):
    def setUp(self):
        self.records = records()
        self.expected = verify.parse_audit(encode(self.records), ["Fixture"])

    def rejects(self, values, expected=None):
        with self.assertRaises(verify.VerificationError):
            verify.parse_audit(encode(values), ["Fixture"], self.expected if expected is None else expected)

    def test_valid_complete_audit(self):
        self.assertEqual(verify.parse_audit(encode(self.records), ["Fixture"], self.expected), self.expected)

    def test_missing_entire_output(self):
        with self.assertRaises(verify.VerificationError):
            verify.parse_audit("", ["Fixture"], self.expected)

    def test_malformed_json(self):
        with self.assertRaises(verify.VerificationError):
            verify.parse_audit(encode(self.records).replace('{"event":', '{"event"'), ["Fixture"], self.expected)

    def test_unexpected_success_text_is_not_audit(self):
        with self.assertRaises(verify.VerificationError):
            verify.parse_audit("PASS: proof checked\n" + encode(self.records), ["Fixture"], self.expected)

    def test_missing_footer(self):
        self.rejects(self.records[:-1])

    def test_wrong_footer_count(self):
        self.records[-1]["count"] = 999
        self.rejects(self.records)

    def test_duplicate_declaration(self):
        self.records.insert(2, self.records[1])
        self.records[-1]["count"] = 3
        self.rejects(self.records)

    def test_missing_owned_helper_even_with_repaired_count(self):
        del self.records[1]
        self.records[-1]["count"] = 1
        self.rejects(self.records)

    def test_custom_axiom(self):
        self.records[1]["axioms"] = ["Fixture.assumption"]
        self.rejects(self.records)

    def test_sorry_axiom(self):
        self.records[1]["axioms"] = ["sorryAx"]
        self.rejects(self.records)

    def test_unsafe_declaration(self):
        self.records[1]["unsafe"] = True
        self.rejects(self.records)

    def test_unsafe_certification_axiom(self):
        self.records[1]["axioms"] = ["Lean.ofReduceBool"]
        self.rejects(self.records)

    def test_owned_axiom_even_if_unused(self):
        self.records[1]["kind"] = "axiom"
        self.rejects(self.records)

    def test_missing_closure(self):
        del self.records[-2]
        self.rejects(self.records)

    def test_closure_missing_helper(self):
        self.records[-2]["names"].remove("Fixture.helper")
        self.rejects(self.records)

    def test_altered_dependency_pin(self):
        manifest = {"packages": [{"name": n, "type": "git", "rev": r} for n, r in verify.PACKAGE_PINS.items()]}
        verify.validate_manifest(manifest)
        manifest["packages"][0]["rev"] = "0" * 40
        with self.assertRaises(verify.VerificationError):
            verify.validate_manifest(manifest)

    def test_missing_dependency(self):
        manifest = {"packages": [{"name": n, "type": "git", "rev": r} for n, r in verify.PACKAGE_PINS.items()]}
        manifest["packages"].pop()
        with self.assertRaises(verify.VerificationError):
            verify.validate_manifest(manifest)

    def test_wrong_lean_version(self):
        with self.assertRaises(verify.VerificationError):
            verify.validate_version("Lean (version 4.20.0, test)\n")

    def test_changed_frozen_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Solution.lean"
            source.write_text("theorem ok : True := True.intro\n")
            expected = {"Solution.lean": hashlib.sha256(source.read_bytes()).hexdigest()}
            verify.verify_hashes(root, expected)
            source.write_text("theorem ok : True := by sorry\n")
            with self.assertRaises(verify.VerificationError):
                verify.verify_hashes(root, expected)

    def test_supplemental_source_must_be_registered(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Solution.lean").write_text("theorem ok : True := True.intro\n")
            (root / "Review.lean").write_text("import Solution\n#check ok\n")
            with self.assertRaises(verify.VerificationError):
                verify.validate_source_inventory(root, {"Solution": "Solution.lean"}, [], {})

    def test_supplemental_source_hash_is_binding(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Solution.lean").write_text("theorem ok : True := True.intro\n")
            source = root / "Review.lean"
            source.write_text("import Solution\n#check ok\n")
            registered = {"Review.lean": hashlib.sha256(source.read_bytes()).hexdigest()}
            verify.validate_source_inventory(root, {"Solution": "Solution.lean"}, [], registered)
            source.write_text("import Solution\naxiom extra : False\n")
            with self.assertRaises(verify.VerificationError):
                verify.validate_source_inventory(root, {"Solution": "Solution.lean"}, [], registered)

    def test_source_policy_handles_nested_comments(self):
        verify.source_policy('/- unsafe /- axiom -/ sorry -/\ntheorem ok : True := True.intro -- admit\n')

    def test_source_policy_rejects_native_certification(self):
        with self.assertRaises(verify.VerificationError):
            verify.source_policy("theorem ok : True := by native_decide\n")

    def test_source_policy_rejects_incomplete_proof(self):
        with self.assertRaises(verify.VerificationError):
            verify.source_policy("theorem ok : True := by sorry\n")

    def test_optimization_cannot_disable_guard(self):
        environment = dict(os.environ)
        environment["PYTHONOPTIMIZE"] = "1"
        environment["PYTHONPATH"] = str(Path(verify.__file__).resolve().parent)
        result = subprocess.run([sys.executable, "-O", "-c", "import verify; verify.validate_python_runtime()"],
                                env=environment, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Python optimization is forbidden", result.stderr)

    def test_optimized_cli_fails_before_verification(self):
        environment = dict(os.environ)
        environment["PYTHONOPTIMIZE"] = "1"
        result = subprocess.run([sys.executable, "-O", str(Path(verify.__file__)),
                                 "--project", "/nonexistent-project", "--lean", str(LEAN),
                                 "--dependencies", "/nonexistent-dependencies", "--logs", "/nonexistent-logs"],
                                env=environment, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Python optimization is forbidden", result.stderr)

    def test_original_audit_missing_owned_helper(self):
        with tempfile.TemporaryDirectory() as directory:
            closure = Path(directory) / "closure.txt"
            closure.write_text("Fixture.helper\nFixture.result\n")
            output = "OWNED Fixture.result\nPASS: inspected 2 owned declarations, including generated helpers\n"
            with self.assertRaises(verify.VerificationError):
                verify.validate_original_audit(output, self.expected, ["Fixture.helper", "Fixture.result"], closure)

    def test_original_audit_missing_summary(self):
        with tempfile.TemporaryDirectory() as directory:
            closure = Path(directory) / "closure.txt"
            closure.write_text("Fixture.helper\nFixture.result\n")
            output = "OWNED Fixture.helper\nOWNED Fixture.result\n"
            with self.assertRaises(verify.VerificationError):
                verify.validate_original_audit(output, self.expected, ["Fixture.helper", "Fixture.result"], closure)


class RealLeanTests(unittest.TestCase):
    def compile_fixture(self, source, audit=True):
        with tempfile.TemporaryDirectory(prefix="tlmc-verifier-test-") as directory:
            root = Path(directory)
            (root / "Fixture.lean").write_text(source)
            env = dict(os.environ)
            env["LEAN_PATH"] = str(root)
            compiled = subprocess.run([str(LEAN), "-DwarningAsError=true", "-o", "Fixture.olean", "Fixture.lean"],
                                      cwd=root, env=env, capture_output=True, text=True, timeout=120)
            if not audit or compiled.returncode:
                return compiled
            (root / "AuditFixture.lean").write_text(verify.audit_source(["Fixture"]))
            return subprocess.run([str(LEAN), "-DwarningAsError=true", "AuditFixture.lean"],
                                  cwd=root, env=env, capture_output=True, text=True, timeout=120)

    def test_valid_proof_and_actual_ownership_inventory(self):
        result = self.compile_fixture("namespace Fixture\ntheorem helper : True := True.intro\ntheorem result : True := helper\nend Fixture\n")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        inventory = verify.parse_audit(result.stdout, ["Fixture"])
        self.assertEqual({x["name"] for x in inventory}, {"Fixture.helper", "Fixture.result"})

    def test_warning_as_error_rejects_sorry(self):
        result = self.compile_fixture("theorem incomplete : True := by sorry\n", audit=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("sorry", result.stdout + result.stderr)

    def test_kernel_rejects_wrong_proof(self):
        result = self.compile_fixture("theorem wrong : False := True.intro\n", audit=False)
        self.assertNotEqual(result.returncode, 0)

    def test_real_custom_axiom_rejected(self):
        result = self.compile_fixture("axiom invented : False\ntheorem wrong : False := invented\n")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Unapproved transitive axiom", result.stdout + result.stderr)

    def test_real_unsafe_declaration_rejected(self):
        result = self.compile_fixture("unsafe def forbidden : Bool := true\ntheorem harmless : True := True.intro\n")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Unsafe transitive declaration", result.stdout + result.stderr)

    def test_real_native_certification_rejected(self):
        result = self.compile_fixture("import Lean\ntheorem nativeCertified : (2 : Nat) = 2 := by native_decide\n")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Unapproved transitive axiom: Lean.ofReduceBool", result.stdout + result.stderr)
        self.assertIn("nativeCertified._nativeDecide_1", result.stdout + result.stderr)

    def test_real_missing_helper_rejected_even_with_repaired_footer(self):
        result = self.compile_fixture("theorem helper : True := True.intro\ntheorem result : True := helper\n")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        expected = verify.parse_audit(result.stdout, ["Fixture"])
        values = [json.loads(line[len(verify.PREFIX):]) for line in result.stdout.splitlines()]
        values = [x for x in values if x.get("name") != "helper"]
        values[-1]["count"] -= 1
        with self.assertRaises(verify.VerificationError):
            verify.parse_audit(encode(values), ["Fixture"], expected)


def main():
    global LEAN
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=Path, required=True)
    args = parser.parse_args()
    LEAN = args.lean.resolve()
    suite = unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__])
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    raise SystemExit(main())
