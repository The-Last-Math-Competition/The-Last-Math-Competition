#!/usr/bin/env python3
"""Behavioral failure-path tests for the separately supplied replay driver.

Run with --project PATH. All modifications occur in a temporary copied project.
Real subprocess tests exercise command capture. Main-driver tests stub only
external Lean/Git operations so integrity and report-handling paths are isolated.
Actual Lean audit controls are performed separately by run_lean_controls.py.
"""
from __future__ import annotations

import argparse
import contextlib
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

parser = argparse.ArgumentParser()
parser.add_argument('--project', required=True, type=Path)
args, remaining = parser.parse_known_args()
PROJECT = args.project.resolve()
spec = importlib.util.spec_from_file_location('subject_replay', PROJECT / 'scripts/replay.py')
replay = importlib.util.module_from_spec(spec)
spec.loader.exec_module(replay)


class ReplayTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='replay-test-', dir=Path(__file__).resolve().parents[1])
        self.root = Path(self.tmp.name)
        for name in ['source', 'scripts']:
            shutil.copytree(PROJECT / name, self.root / name)
        for name in ['Conjecture1624.lean', 'Verification.lean', 'Audit.lean', 'lean-toolchain', 'lake-manifest.json', 'lakefile.lean']:
            shutil.copyfile(PROJECT / name, self.root / name)
        (self.root / 'records').mkdir()
        (self.root / 'runtime').mkdir()
        for name in ['lean', 'lake']:
            (self.root / 'runtime' / name).write_text('fixture binary; never executed\n')
        self.patches = [patch.object(replay, 'ROOT', self.root), patch.object(replay, 'RECORDS', self.root / 'records')]
        for p in self.patches:
            p.start()

    def tearDown(self):
        for p in reversed(self.patches):
            p.stop()
        self.tmp.cleanup()

    def run_real(self, code):
        results = []
        try:
            out = replay.run([sys.executable, '-c', code], 'control', dict(os.environ), results)
            return out, results
        finally:
            self.assertEqual(len(results), 1)
            log = self.root / results[0]['log']
            self.assertEqual(hashlib.sha256(log.read_bytes()).hexdigest(), results[0]['log_sha256'])

    def test_real_success_output_is_recorded(self):
        out, rows = self.run_real("print('checked output')")
        self.assertEqual(out, 'checked output\n')
        self.assertEqual(rows[0]['returncode'], 0)

    def test_real_failed_command_rejected_and_logged(self):
        with self.assertRaisesRegex(RuntimeError, 'failed with exit 7'):
            self.run_real("import sys; print('expected failure', file=sys.stderr); sys.exit(7)")
        self.assertIn('expected failure', (self.root / 'records/replay-control.log').read_text())

    def test_real_warning_rejected_even_with_zero_exit(self):
        with self.assertRaisesRegex(RuntimeError, 'emitted a warning'):
            self.run_real("print('Verification.lean:3:2: warning: sentinel')")

    def test_scanner_ignores_nested_comments_strings_but_preserves_live_text(self):
        source = '/- sorry /- axiom -/ unsafe -/\n-- admit\ndef s := "native_decide \\" sorry"\naxiom live : True\n'
        scanned = replay.strip_lean_comments_strings(source)
        self.assertEqual(scanned.count('\n'), source.count('\n'))
        self.assertNotIn('native_decide', scanned)
        self.assertNotIn('sorry', scanned)
        self.assertNotIn('unsafe', scanned)
        self.assertIn('axiom live : True', scanned)

    def test_scanner_separates_adjacent_tokens_and_rejects_unterminated_input(self):
        self.assertEqual(replay.strip_lean_comments_strings('a/- nested -/b'), 'a b')
        for source in ['/- outer /- inner -/', 'def s := "unterminated']:
            with self.subTest(source=source), self.assertRaisesRegex(RuntimeError, 'Unterminated'):
                replay.strip_lean_comments_strings(source)

    def main_control(self, *, audit=None, emit_audit=True, audit_symlink=False, dirty=False, wrong_rev=False):
        packages = json.loads((self.root / 'source/lake-manifest.json').read_text())['packages']
        revs = {p['name']: p['rev'] for p in packages}
        default_audit = {'status': 'PASS', 'owned_count': 1, 'dependency_count': 1,
                         'axioms': [], 'forbidden_axioms': [], 'unsafe_dependencies': [],
                         'partial_dependencies': [], 'imported_modules': []}
        report = default_audit if audit is None else audit

        def git_output(command, **kwargs):
            if command[-2:] == ['rev-parse', 'HEAD']:
                return ('0' * 40 if wrong_rev else revs[Path(command[2]).name]) + '\n'
            return ' M changed.lean\n' if dirty else ''

        def external_run(command, label, env, results):
            if label == 'version':
                return 'Lean (version 4.19.0, aarch64-apple-darwin, Release)\n'
            if label == 'audit' and emit_audit:
                path = self.root / 'records/dependency-audit.json'
                if audit_symlink:
                    target = self.root / 'external-report.json'
                    target.write_text(json.dumps(report))
                    path.symlink_to(target)
                else:
                    path.write_text(json.dumps(report))
            return ''

        error = None
        with patch.object(sys, 'argv', ['replay.py', '--lean-bin', str(self.root / 'runtime')]), \
             patch.object(replay.subprocess, 'check_output', side_effect=git_output), \
             patch.object(replay, 'run', side_effect=external_run), contextlib.redirect_stdout(io.StringIO()):
            try:
                replay.main()
            except Exception as exc:
                error = exc
        summary = json.loads((self.root / 'records/replay-result.json').read_text())
        return error, summary

    def assert_rejected(self, **kwargs):
        error, summary = self.main_control(**kwargs)
        self.assertIsNotNone(error, 'replay unexpectedly accepted invalid fixture')
        self.assertEqual(summary['status'], 'FAIL')
        self.assertTrue(summary.get('error'))
        return summary

    def test_control_fixture_passes(self):
        error, summary = self.main_control()
        self.assertIsNone(error)
        self.assertEqual(summary['status'], 'PASS')

    def test_changed_input_rejected(self):
        (self.root / 'source/ORIGINAL.md').write_text('changed problem statement\n')
        self.assertIn('hash mismatch', self.assert_rejected()['error'])

    def test_missing_input_digest_rejected(self):
        path = self.root / 'source/SHA256SUMS.json'
        sums = json.loads(path.read_text())
        del sums['ORIGINAL.md']
        path.write_text(json.dumps(sums))
        self.assert_rejected()

    def test_changed_toolchain_rejected(self):
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:v4.20.0\n')
        self.assert_rejected()

    def test_self_consistent_changed_input_and_digest_rejected(self):
        original = self.root / 'source/ORIGINAL.md'
        original.write_text('changed problem statement\n')
        path = self.root / 'source/SHA256SUMS.json'
        sums = json.loads(path.read_text())
        sums['ORIGINAL.md'] = hashlib.sha256(original.read_bytes()).hexdigest()
        path.write_text(json.dumps(sums))
        self.assert_rejected()

    def test_changed_package_pin_rejected(self):
        path = self.root / 'lake-manifest.json'
        manifest = json.loads(path.read_text())
        manifest['packages'][0]['rev'] = '0' * 40
        path.write_text(json.dumps(manifest))
        self.assert_rejected()

    def test_redirected_package_directory_rejected(self):
        path = self.root / 'lake-manifest.json'
        manifest = json.loads(path.read_text())
        manifest['packagesDir'] = '.lake/unverified'
        path.write_text(json.dumps(manifest))
        self.assert_rejected()

    def test_wrong_checkout_revision_rejected(self):
        self.assert_rejected(wrong_rev=True)

    def test_dirty_package_source_rejected(self):
        self.assert_rejected(dirty=True)

    def test_live_prohibited_source_rejected(self):
        path = self.root / 'Verification.lean'
        path.write_text(path.read_text() + '\naxiom injected : False\n')
        self.assertIn('Prohibited source construct', self.assert_rejected()['error'])

    def test_stale_pass_report_cannot_replace_new_audit(self):
        error, _ = self.main_control()
        self.assertIsNone(error)
        self.assert_rejected(emit_audit=False)

    def test_audit_failure_fields_each_rejected(self):
        for field in ['forbidden_axioms', 'unsafe_dependencies', 'partial_dependencies']:
            with self.subTest(field=field):
                report = {'status': 'PASS', 'owned_count': 1, 'dependency_count': 1,
                          'axioms': [], 'forbidden_axioms': [], 'unsafe_dependencies': [],
                          'partial_dependencies': [], 'imported_modules': []}
                report[field] = ['Injected.bad']
                self.assert_rejected(audit=report)

    def test_malformed_audit_rejected(self):
        self.assert_rejected(audit={'status': 'PASS'})

    def test_symlinked_audit_rejected(self):
        self.assert_rejected(audit_symlink=True)

    def test_symlinked_owned_build_rejected_before_deletion(self):
        target = self.root / 'external-build'
        target.mkdir()
        sentinel = target / 'preserve'
        sentinel.write_text('must survive\n')
        (self.root / '.lake').mkdir()
        (self.root / '.lake/build').symlink_to(target, target_is_directory=True)
        self.assert_rejected()
        self.assertTrue(sentinel.exists())


if __name__ == '__main__':
    unittest.main(argv=[sys.argv[0]] + remaining, verbosity=2)
