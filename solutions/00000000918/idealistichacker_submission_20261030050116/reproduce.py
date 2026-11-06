"""Exact #918 reproduction. Installed toolchain and official dependency caches remain trust inputs. Only this own project's build is cleared; no final PDF/review/acceptance or full-dependency-clean claim."""
from __future__ import annotations
import argparse
from collections import Counter
from contextlib import contextmanager
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import signal
import stat
import subprocess
import sys
import time
SPEC_PENDING = False
CID = '00000000918'
PIN = 'leanprover/lean4:v4.33.1'
SOURCE_COMMIT = 'b355e42906e6eaf52bc7e9d005e0ef02d8aa7400'
SOURCE_BLOB = 'dadc2ef65f6a57feb3def12febafd66299b1f918'
SOURCE_SHA256 = '326b3e1b5e32b83188a2648a49b823f81b6d8ae7a0a6af46d08a71338998676f'
MATHLIB = '0df444a360eaa60ab8c11dca51a86af692955474'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
NAME = '[A-Za-z_][A-Za-z_0-9]*'
QUALIFIED = NAME + '(?:\\.' + NAME + ')*'
MODULES = {'NuclearCPAP': 'Quasitrace918', 'TraceTriangle': 'Quasitrace918', 'MatrixExtensions': 'Quasitrace918', 'QuasiTraceModel': 'Quasitrace918', 'Main': 'Quasitrace918'}
MATH_HASHES = {'NuclearCPAP': '8f3b764e6f1091273c1a79a5d32c28de27ddac248529e55f5b118c88eea22d86', 'TraceTriangle': 'b5cc2c197c99ede3fe3aeb4c4f5eaf3f23c77bf9b131d5380b85e35660b72d61', 'MatrixExtensions': '4de47655ec322c0f31a06512228bb74d41a0abc86390e2ec80b0acdf55596e01', 'QuasiTraceModel': '3e8d5863b50cd283fa1720bb696efbd4ac894e5f20193f0157f25745a4f8b43c', 'Main': '3129fb5877bd64b6f9f178c267a32c436bb2a840ef77c26b57f30ea33b04d0e6'}
THEOREMS = ('Quasitrace918.actual_model_hasCPAP', 'Quasitrace918.actual_nuclear_counterexample', 'Quasitrace918.affineSpan_direction_finrank_ge_two', 'Quasitrace918.affineSpan_direction_finrank_ne_one', 'Quasitrace918.algebra_complex_finite', 'Quasitrace918.complex_linear_trace_oneQuasitrace', 'Quasitrace918.coordinate_add', 'Quasitrace918.coordinate_apply', 'Quasitrace918.coordinate_atom', 'Quasitrace918.coordinate_continuous', 'Quasitrace918.coordinate_difference_mem_vectorSpan', 'Quasitrace918.coordinate_mem_normalizedQuasitraces', 'Quasitrace918.coordinate_mem_traceStates', 'Quasitrace918.coordinate_mem_weakQuasitraces', 'Quasitrace918.coordinate_mul', 'Quasitrace918.coordinate_norm_bound', 'Quasitrace918.coordinate_one', 'Quasitrace918.coordinate_oneQuasitrace', 'Quasitrace918.coordinate_operator_norm', 'Quasitrace918.coordinate_positive', 'Quasitrace918.coordinate_smul', 'Quasitrace918.coordinate_star', 'Quasitrace918.coordinate_star_square_imag', 'Quasitrace918.coordinate_star_square_real', 'Quasitrace918.coordinate_tracial', 'Quasitrace918.coordinate_triangle_finrank', 'Quasitrace918.coordinate_twoQuasitrace', 'Quasitrace918.coordinate_weak_continuous', 'Quasitrace918.coordinates_real_affineIndependent', 'Quasitrace918.coordinates_real_linearIndependent', 'Quasitrace918.dualToFunction_injective', 'Quasitrace918.exact_cpc_factorization', 'Quasitrace918.finite_dimensional_hasCPAP', 'Quasitrace918.identityCP_apply', 'Quasitrace918.identityCP_cpc', 'Quasitrace918.identityCP_matrix_nonneg', 'Quasitrace918.matrixCoordinate_add', 'Quasitrace918.matrixCoordinate_apply', 'Quasitrace918.matrixCoordinate_continuous', 'Quasitrace918.matrixCoordinate_corner', 'Quasitrace918.matrixCoordinate_cyclic_star_square', 'Quasitrace918.matrixCoordinate_isSelfAdjoint', 'Quasitrace918.matrixCoordinate_normSq', 'Quasitrace918.matrixCoordinate_one', 'Quasitrace918.matrixCoordinate_oneQuasitrace', 'Quasitrace918.matrixCoordinate_positive', 'Quasitrace918.matrixCoordinate_smul', 'Quasitrace918.matrixCoordinate_star', 'Quasitrace918.matrixCoordinate_star_square', 'Quasitrace918.matrixCoordinate_star_square_imag', 'Quasitrace918.matrixCoordinate_trace', 'Quasitrace918.matrixCoordinate_tracial', 'Quasitrace918.matrixCorner_add', 'Quasitrace918.matrixCorner_smul', 'Quasitrace918.normalized_quasitrace_dimension_ge_two', 'Quasitrace918.normalized_quasitrace_dimension_ne_one', 'Quasitrace918.normalized_space_membership', 'Quasitrace918.oneQuasitrace_additive', 'Quasitrace918.oneQuasitrace_subadditive_real', 'Quasitrace918.oneQuasitrace_unique_dual_representation', 'Quasitrace918.ordinaryTraceStates_dimension_ge_two', 'Quasitrace918.ordinaryTraceStates_dimension_ne_one', 'Quasitrace918.source_necessary_clause_false', 'Quasitrace918.unbundled_iff_unique_dual', 'Quasitrace918.unbundled_space_eq_linear_image', 'Quasitrace918.unnormalized_quasitrace_dimension_ne_one', 'Quasitrace918.vectorSpan_finrank_ge_two', 'Quasitrace918.vectorSpan_finrank_ne_one')
DEFINITIONS = ('Quasitrace918.A', 'Quasitrace918.CPC', 'Quasitrace918.FiniteCStarModel', 'Quasitrace918.FiniteCStarModel.carrier', 'Quasitrace918.FiniteCStarModel.instCStar', 'Quasitrace918.FiniteCStarModel.instFinite', 'Quasitrace918.FiniteCStarModel.instOrder', 'Quasitrace918.FiniteCStarModel.instStarOrder', 'Quasitrace918.FiniteCStarModel.mk', 'Quasitrace918.FiniteCommutativeDimensionOneClause', 'Quasitrace918.HasCPAP', 'Quasitrace918.MatrixA', 'Quasitrace918.OneQuasitrace', 'Quasitrace918.TraceDual', 'Quasitrace918.TwoQuasitrace', 'Quasitrace918.WeakContinuous', 'Quasitrace918.algebra_is_comm_cstar', 'Quasitrace918.atom', 'Quasitrace918.coordinate', 'Quasitrace918.cornerOf', 'Quasitrace918.dualToFunction', 'Quasitrace918.finiteModel', 'Quasitrace918.identityCP', 'Quasitrace918.matrixA_complex_finite', 'Quasitrace918.matrixA_cstar', 'Quasitrace918.matrixBaseOrder', 'Quasitrace918.matrixBaseStarOrdered', 'Quasitrace918.matrixCoordinate', 'Quasitrace918.matrixCoordinateEntries', 'Quasitrace918.matrixCoordinateLinear', 'Quasitrace918.matrixCorner', 'Quasitrace918.normalizedTwoQuasitraces', 'Quasitrace918.normalizedWeakQuasitraceSpace', 'Quasitrace918.ordinaryTraceStates', 'Quasitrace918.traceDual_complex_finite', 'Quasitrace918.traceDual_real_finite', 'Quasitrace918.unbundledNormalizedQuasitraces', 'Quasitrace918.weakTwoQuasitraces')
DEPENDENCIES = (('mathlib', 'https://github.com/leanprover-community/mathlib4.git', '0df444a360eaa60ab8c11dca51a86af692955474', '0df444a360eaa60ab8c11dca51a86af692955474', '', 'lakefile.lean'), ('plausible', 'https://github.com/leanprover-community/plausible', 'b7eb3304aeae834b12dda98993a37f6a41f6f0bb', 'main', 'leanprover-community', 'lakefile.toml'), ('LeanSearchClient', 'https://github.com/leanprover-community/LeanSearchClient', '5f4d51b81cbd3f6b32b156bfad9056621a040404', 'main', 'leanprover-community', 'lakefile.toml'), ('importGraph', 'https://github.com/leanprover-community/import-graph', '16f02aa7642864af59f1ff0e384a015994db9118', 'main', 'leanprover-community', 'lakefile.toml'), ('proofwidgets', 'https://github.com/leanprover-community/ProofWidgets4', '4be2e3d5087eeb272cf5a8853b8f9dd025ef5957', 'main', 'leanprover-community', 'lakefile.lean'), ('aesop', 'https://github.com/leanprover-community/aesop', '3448c0bcc5ce01b2d1546e483ec3620e32df3d0e', 'master', 'leanprover-community', 'lakefile.toml'), ('Qq', 'https://github.com/leanprover-community/quote4', '92c15be17b7caf78c2ad767ec40f89052d908d81', 'master', 'leanprover-community', 'lakefile.toml'), ('batteries', 'https://github.com/leanprover-community/batteries', '4488d40d070b9700d4d5a6aa342f0d40c31b2a2d', 'main', 'leanprover-community', 'lakefile.toml'), ('Cli', 'https://github.com/leanprover/lean4-cli', '6130a47896ce867c6a4a55373441e59e565bad0f', 'v4.33.0', 'leanprover', 'lakefile.toml'))
WINDOWS_LINKTEXT = {'mathlib': {b'scripts/bench/build/fake-root/bin/lean.py': b'819298943e1a8c331413fb55e2c4bbc98d05e562', b'scripts/bench/size/run.py': b'e5224d533ef27b001224859a9b36696846a7e7fe'}, 'batteries': {b'docs/README.md': b'32d46ee883b58d6a383eed06eb98f33aa6530ded'}}
LAKEFILE = 'import Lake\nopen Lake DSL\n\npackage tlmc918 where\n  srcDir := "."\n\nrequire mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"\n\n@[default_target]\nlean_lib TLMC918 where\n  roots := #[`NuclearCPAP, `TraceTriangle, `MatrixExtensions, `QuasiTraceModel, `Main, `Check, `CheckDefinitions]\n  moreLeanArgs := #["-DwarningAsError=true"]'
CHECKS_SHA256 = 'ee296780faf533fdb3575de53e0a74cb6703ad1a616ec4270dd04e18a80e6d79'
LAKE_BIN = None
DEADLINE = None
PROFILE_RECORDS = []
RUNTIME_KEYS = ('PATH', 'LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LAKE_HOME', 'LD_LIBRARY_PATH', 'DYLD_LIBRARY_PATH')
ATTRIBUTES = 'lean4/*.lean text eol=lf\nlean4/lean-toolchain text eol=lf\nlean4/lake-manifest.json text eol=lf\n*.py text eol=lf\nsource.md text eol=lf\nmain.tex text eol=lf\nmain.pdf -text\n'

class ReproductionError(RuntimeError):
    pass

def require(condition: bool, message: str) -> None:
    if not condition:
        raise ReproductionError(message)

def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def check_deadline() -> None:
    require(DEADLINE is None or time.monotonic() < DEADLINE, 'Reproduction wall-clock budget exceeded')

@contextmanager
def phase(name: str):
    started = time.monotonic_ns()
    status = 'error'
    try:
        yield
        status = 'ok'
    finally:
        record = {'phase': name, 'status': status, 'duration_ms': (time.monotonic_ns() - started) // 1000000}
        PROFILE_RECORDS.append(record)
        print('[PROFILE] ' + json.dumps(record, ensure_ascii=True), flush=True)

def lexical_component(name: str) -> None:
    require(name not in {'', '.', '..'}, 'Dot/empty path alias rejected')
    if os.name == 'nt':
        require(not name.endswith(('.', ' ')) and ':' not in name, 'Windows path alias/stream rejected: ' + name)
        require(name.split('.', 1)[0].upper() not in {'CON', 'PRN', 'AUX', 'NUL', *('COM' + str(i) for i in range(1, 10)), *('LPT' + str(i) for i in range(1, 10))}, 'Windows device path rejected')

def safe_path(path: Path, checked_parents: set[Path] | None=None) -> Path:
    """Generic paths resolve fully; only canonical ordinary directories are memoized."""
    if os.name == 'nt':
        require(not path.drive or bool(path.root), 'Drive-relative path rejected before absolute resolution')
    for component in path.parts:
        if component != path.anchor:
            lexical_component(component)
    absolute = Path(os.path.abspath(path))
    part, directories = (absolute, [])
    while True:
        if part != absolute and checked_parents is not None and (part in checked_parents):
            break
        try:
            info = part.lstat()
        except FileNotFoundError:
            info = None
        if info is not None:
            require(not stat.S_ISLNK(info.st_mode) and (not getattr(info, 'st_file_attributes', 0) & 1024), 'Symlink/reparse path rejected: ' + str(part))
            if stat.S_ISDIR(info.st_mode):
                directories.append(part)
        if part.parent == part:
            break
        part = part.parent
    require(absolute.resolve() == absolute, 'Path resolution changed the checked boundary')
    if checked_parents is not None:
        checked_parents.update(directories)
    return absolute

def audit_tree_entries(root: Path, checked_parents: set[Path]) -> set[Path]:
    """Walk every entry, including caches/.git, without resolving each ordinary file.

    scandir's non-following stat supplies lstat metadata for each freshly enumerated
    entry. Exact names under resolved directories establish the file boundary.
    Only directory canonicality is memoized within this invocation's audit pass.
    """
    root = safe_path(root, checked_parents)
    require(root.is_dir(), 'Audit tree root is not a directory')
    pending, files = ([root], set())
    entries_count, directories_count = (0, 0)
    while pending:
        check_deadline()
        parent = safe_path(pending.pop(), checked_parents)
        require(parent.is_relative_to(root), 'Audit directory escaped checked boundary')
        directories_count += 1
        with os.scandir(parent) as entries:
            for entry in entries:
                check_deadline()
                lexical_component(entry.name)
                info = entry.stat(follow_symlinks=False)
                require(not stat.S_ISLNK(info.st_mode) and (not getattr(info, 'st_file_attributes', 0) & 1024), 'Symlink/reparse path rejected: ' + str(parent / entry.name))
                path = parent / entry.name
                require(path.is_relative_to(root), 'Audit entry escaped checked boundary')
                entries_count += 1
                if stat.S_ISDIR(info.st_mode):
                    pending.append(path)
                else:
                    require(stat.S_ISREG(info.st_mode), 'Non-regular audit tree entry')
                    files.add(path)
    print('[PROFILE] ' + json.dumps({'phase': 'tree.entries', 'root': str(root), 'entries': entries_count, 'directories': directories_count}, ensure_ascii=True), flush=True)
    return files

def tracked_file_path(checkout: Path, relative: bytes, files: set[Path], checked_parents: set[Path]) -> Path:
    text = relative.decode('utf-8', errors='strict')
    require('\\' not in text and (not text.startswith('/')), 'Aliased tracked path rejected')
    for component in text.split('/'):
        lexical_component(component)
    path = checkout / text
    require(path.is_relative_to(checkout) and path in files and (path.parent in checked_parents), 'Tracked path not an exact enumerated file under a canonical parent')
    info = path.lstat()
    require(stat.S_ISREG(info.st_mode) and (not getattr(info, 'st_file_attributes', 0) & 1024), 'Unsafe/missing tracked dependency file')
    return path

def git(repo: Path, *args: str) -> bytes:
    return run(['git', '--no-pager', '-c', 'credential.helper=', '-c', 'core.fsmonitor=false', '-C', str(repo), *args], repo)

def validate_source(package: Path, repo: Path, m: dict) -> dict:
    for key, expected in (('source_commit', SOURCE_COMMIT), ('source_git_blob', SOURCE_BLOB), ('source_sha256', SOURCE_SHA256)):
        require(m.get(key) == expected, 'Frozen source manifest mismatch: ' + key)
    source_name = 'conjectures/' + CID + '.md'
    require(git(repo, 'cat-file', '-t', SOURCE_COMMIT).strip() == b'commit', 'Source object is not a commit')
    require(git(repo, 'rev-parse', SOURCE_COMMIT + ':' + source_name).strip().decode() == SOURCE_BLOB, 'Source commit does not bind the advertised blob')
    require(git(repo, 'cat-file', '-t', SOURCE_BLOB).strip() == b'blob', 'Source object is not a blob')
    raw = git(repo, 'cat-file', 'blob', SOURCE_BLOB)
    require(sha256(raw) == SOURCE_SHA256, 'Raw source SHA-256 mismatch')
    require(hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\x00' + raw).hexdigest() == SOURCE_BLOB, 'Raw source Git-blob hash mismatch')
    require(safe_path(package / 'source.md').read_bytes() == raw, 'Frozen source differs from raw Git blob')
    current = safe_path(repo / source_name).read_bytes()
    require(current.replace(b'\r\n', b'\n') == raw.replace(b'\r\n', b'\n'), 'Current bilingual source differs (CRLF-to-LF comparison)')
    raw.decode('utf-8', errors='strict')
    return {'commit': SOURCE_COMMIT, 'blob': SOURCE_BLOB, 'raw_sha256': SOURCE_SHA256}

def expected_lock() -> dict:
    return {'version': '1.2.0', 'packagesDir': '.lake/packages', 'name': 'tlmc918', 'lakeDir': '.lake', 'fixedToolchain': False, 'packages': [{'name': name, 'type': 'git', 'url': url, 'rev': rev, 'inputRev': input_rev, 'subDir': None, 'scope': scope, 'manifestFile': 'lake-manifest.json', 'inherited': name != 'mathlib', 'configFile': config} for name, url, rev, input_rev, scope, config in DEPENDENCIES]}

def validate_config(lean: Path) -> dict:
    require(safe_path(lean / 'lean-toolchain').read_text(encoding='utf-8').strip() == PIN, 'Exact Lean toolchain pin required')
    require(not os.path.lexists(lean / 'lakefile.toml'), 'Unexpected alternate Lake configuration')
    require(safe_path(lean / 'lakefile.lean').read_text(encoding='utf-8').strip() == LAKEFILE, 'Declarative Lake configuration/roots changed')
    lock = json.loads(safe_path(lean / 'lake-manifest.json').read_text(encoding='utf-8'))
    require(lock == expected_lock(), 'Exact nine-package Lake lock/configuration mismatch')
    return lock

def dependency_mode_allowed(name: str, mode: bytes, relative: bytes) -> bool:
    return mode in {b'100644', b'100755'} or (os.name == 'nt' and mode == b'120000' and (relative in WINDOWS_LINKTEXT.get(name, set())))

def materialized_dependencies(lean: Path, lock: dict) -> dict:
    require(lock == expected_lock(), 'Refuse non-frozen dependency specifications')
    reports = {}
    checked_parents: set[Path] = set()
    for spec in lock['packages']:
        name = spec['name']
        checkout = safe_path(lean / '.lake' / 'packages' / name, checked_parents)
        require(checkout.is_dir(), 'Missing physical dependency checkout: ' + name)
        git_dir = safe_path(checkout / '.git', checked_parents)
        require(git_dir.is_dir(), 'Dependency must own a physical .git directory: ' + name)
        with phase('dependency.' + name + '.walk'):
            files = audit_tree_entries(checkout, checked_parents)
        with phase('dependency.' + name + '.git_metadata'):
            require(safe_path(Path(git(checkout, 'rev-parse', '--show-toplevel').decode().strip())) == checkout, 'Dependency inherited/redirected a parent Git checkout: ' + name)
            require(safe_path(Path(git(checkout, 'rev-parse', '--absolute-git-dir').decode().strip())) == git_dir, 'Dependency Git metadata redirected: ' + name)
            require(git(checkout, 'rev-parse', 'HEAD').decode().strip() == spec['rev'], 'Dependency HEAD mismatch: ' + name)
            require(git(checkout, 'remote', 'get-url', 'origin').decode().strip() == spec['url'], 'Dependency origin mismatch: ' + name)
            require(not git(checkout, 'status', '--porcelain=v1', '-z', '--untracked-files=no', '--ignore-submodules=none').strip(), 'Modified tracked dependency source: ' + name)
        with phase('dependency.' + name + '.tracked_bytes_and_tree'):
            tracked = git(checkout, 'ls-files', '--stage', '-z').split(b'\x00')
            require(any(tracked), 'Empty tracked dependency inventory: ' + name)
            tree = {}
            for record in git(checkout, 'ls-tree', '-r', '-z', '--full-tree', 'HEAD').split(b'\x00'):
                if record:
                    header, relative = record.split(b'\t', 1)
                    mode, kind, oid = header.split()
                    require(kind == b'blob' and dependency_mode_allowed(name, mode, relative), 'Non-regular dependency Git tree: ' + name)
                    if mode == b'120000':
                        require(oid == WINDOWS_LINKTEXT[name][relative], 'Fixed inert-link Git blob mismatch')
                    require(relative not in tree, 'Duplicate dependency tree file: ' + name)
                    tree[relative] = (mode, oid)
            indexed = {}
            count = 0
            for record in tracked:
                if not record:
                    continue
                header, relative = record.split(b'\t', 1)
                mode, oid, stage = header.split()
                require(dependency_mode_allowed(name, mode, relative) and stage == b'0', 'Symlink/submodule/unmerged tracked dependency source: ' + name)
                if mode == b'120000':
                    require(oid == WINDOWS_LINKTEXT[name][relative], 'Fixed inert-link index blob mismatch')
                require(relative not in indexed, 'Duplicate tracked dependency file: ' + name)
                indexed[relative] = (mode, oid)
                check_deadline()
                path = tracked_file_path(checkout, relative, files, checked_parents)
                data = path.read_bytes()

                def blob_hash(raw: bytes) -> bytes:
                    return hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\x00' + raw).hexdigest().encode()
                if blob_hash(data) != oid:
                    require(mode != b'120000', 'Inert link-text placeholder changed: ' + name)
                    require(b'\x00' not in data, 'Tracked binary dependency source changed: ' + name)
                    data.decode('utf-8', errors='strict')
                    require(blob_hash(data.replace(b'\r\n', b'\n')) == oid, 'Tracked dependency bytes changed despite Git status: ' + name)
                count += 1
            require(indexed == tree, 'Dependency index differs from the fixed HEAD tree: ' + name)
        reports[name] = {'head': spec['rev'], 'origin': spec['url'], 'clean_tracked_files': count}
    return reports

def scrub_comments(text: str) -> str:
    """Bounded comment lexer; strings are not accepted in authored math/Check."""
    out, i, depth = ([], 0, 0)
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            out.extend('  ')
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            out.extend('  ')
            i += 2
        elif depth:
            out.append('\n' if text[i] == '\n' else ' ')
            i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            out.extend(' ' * (end - i))
            i = end
        else:
            require(text[i] != '"', 'String outside bounded authored Lean dialect')
            out.append(text[i])
            i += 1
    require(depth == 0, 'Unterminated Lean comment')
    return ''.join(out)

def frozen_files(package: Path) -> dict[str, str]:
    checked_parents: set[Path] = set()
    package = safe_path(package, checked_parents)
    files = {}
    for root, dirs, names in os.walk(package, followlinks=False):
        parent = Path(root)
        for directory in dirs:
            safe_path(parent / directory, checked_parents)
        dirs[:] = [d for d in dirs if d != '__pycache__' and (not (parent == package / 'lean4' and d == '.lake'))]
        for name in names:
            if parent == package and name in {'review.json', 'validation.json'}:
                continue
            path = safe_path(parent / name, checked_parents)
            require(stat.S_ISREG(path.stat().st_mode), 'Non-regular authored package file')
            files[path.relative_to(package).as_posix()] = sha256(path.read_bytes())
    return files

def clean_project_build(lean: Path, target: Path | None=None) -> None:
    lean = safe_path(lean)
    expected = lean / '.lake' / 'build'
    target = safe_path(expected if target is None else target)
    require(target == expected and target.is_relative_to(lean), 'Unsafe project cache deletion boundary')
    if not target.exists():
        return
    require(target.is_dir(), 'Project build cache is not a directory')
    checked_parents: set[Path] = set()
    safe_path(target, checked_parents)
    audit_tree_entries(target, checked_parents)
    require(safe_path(target) == expected, 'Deletion boundary changed')
    shutil.rmtree(target)

def audit_axioms(output: str, names: list[str]) -> dict:
    audits = {}
    pattern = "^'(" + QUALIFIED + ")' (?:does not depend on any axioms|depends on axioms:\\s*\\[([^\\]]*)\\])\\s*$"
    for match in re.finditer(pattern, output, re.M):
        name, footprint = (match[1], match[2])
        require(name in names and name not in audits, 'Unexpected/duplicate actual axiom audit')
        used = [] if footprint is None else [a.strip() for a in footprint.split(',')]
        require(set(used) <= ALLOWED_AXIOMS, 'Nonstandard axiom footprint: ' + name)
        audits[name] = sorted(used)
    require(set(audits) == set(names), 'Missing/malformed actual axiom audit')
    return audits

def audit_theorem_types(output: str, names: list[str]) -> dict[str, str]:
    """Capture every actual #check type, rejecting extra or missing output."""
    types, cursor = ({}, 0)
    pattern = "^'(" + QUALIFIED + ")' (?:does not depend on any axioms|depends on axioms:\\s*\\[[^\\]]*\\])\\s*$"
    for audit in re.finditer(pattern, output, re.M):
        name = audit[1]
        require(name in names and name not in types, 'Unexpected/duplicate actual theorem type')
        chunk = output[cursor:audit.start()].strip()
        require(re.match('@?' + re.escape(name) + '(?:\\.\\{[^}\\n]+\\})?(?=\\s|:)', chunk) is not None and ':' in chunk, 'Missing/malformed actual theorem type: ' + name)
        require(all((line[:1].isspace() for line in chunk.splitlines()[1:])), 'Additional diagnostic mixed into theorem type: ' + name)
        types[name] = chunk
        cursor = audit.end()
    require(set(types) == set(names) and (not output[cursor:].strip()), 'Incomplete/additional theorem type output')
    return types

def child_env():
    # Exact finite diagnostics must not silently lose assertions in a child.
    env = {key: os.environ[key] for key in os.environ if not key.upper().startswith(('GH_', 'GITHUB_', 'GIT_', 'GCM_', 'SSH_', 'LEAN_', 'AWS_', 'AZURE_', 'OPENAI_', 'ANTHROPIC_')) and key.upper() != 'LAKE_HOME' and (not any((word in key.upper() for word in ('TOKEN', 'SECRET', 'PASSWORD', 'CREDENTIAL', 'API_KEY', 'ACCESS_KEY', 'AUTH', 'COOKIE', 'PRIVATE_KEY'))))}
    env.update(PYTHONUTF8='1', PYTHONIOENCODING='utf-8', PYTHONDONTWRITEBYTECODE='1', LANG='C.UTF-8', LC_ALL='C.UTF-8', NO_COLOR='1', GIT_TERMINAL_PROMPT='0', GCM_INTERACTIVE='Never', GCM_GUI_PROMPT='Never', GIT_NO_LAZY_FETCH='1', GIT_OPTIONAL_LOCKS='0', GIT_NO_REPLACE_OBJECTS='1', GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_COUNT='2', GIT_CONFIG_KEY_0='credential.helper', GIT_CONFIG_VALUE_0='', GIT_CONFIG_KEY_1='core.fsmonitor', GIT_CONFIG_VALUE_1='false', MATHLIB_NO_CACHE_ON_UPDATE='1')
    if LAKE_BIN is not None:
        env['PATH'] = str(LAKE_BIN) + os.pathsep + env.get('PATH', '')
    env.pop('PYTHONOPTIMIZE', None)
    return env

def run(args, cwd, timeout=120, show_output=False, env=None):
    if DEADLINE is not None:
        remaining = DEADLINE - time.monotonic()
        require(remaining > 0, 'Reproduction wall-clock budget exceeded')
        timeout = min(timeout, remaining)
    options = {'creationflags': subprocess.CREATE_NEW_PROCESS_GROUP} if os.name == 'nt' else {'start_new_session': True}
    process = None
    actual_env = child_env() if env is None else env
    try:
        process = subprocess.Popen(args, cwd=cwd, env=actual_env, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE, **options)
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        if process is not None and process.poll() is None:
            if os.name == 'nt':
                subprocess.run(['taskkill.exe', '/PID', str(process.pid), '/T', '/F'], env=actual_env, stdin=subprocess.DEVNULL, capture_output=True, timeout=15, check=False)
            else:
                os.killpg(process.pid, signal.SIGKILL)
            if process.poll() is None:
                process.kill()
            stdout, stderr = process.communicate(timeout=15)
        else:
            stdout, stderr = (exc.stdout or b'', exc.stderr or b'')
        if stdout or stderr:
            print((stdout + stderr).decode('utf-8', errors='replace'), flush=True)
        raise ReproductionError('Local tool timed out; owned process tree terminated: ' + Path(args[0]).name) from exc
    except OSError as exc:
        raise ReproductionError('Local tool unavailable: ' + Path(args[0]).name) from exc
    if show_output or process.returncode:
        print((stdout + stderr).decode('utf-8', errors='replace'), flush=True)
    require(process.returncode == 0, 'Local command failed (exit ' + str(process.returncode) + '): ' + Path(args[0]).name)
    return stdout

def query_source(names):
    return 'import Main\n\n' + ''.join(('#check ' + n + '\n#print axioms ' + n + '\n' for n in names))

def theorem_names(manifest):
    names = manifest.get('theorems')
    require(isinstance(names, list) and Counter(names) == Counter(THEOREMS), 'Manifest must list exactly all 68 frozen theorems')
    require(manifest.get('audited_definitions') == list(DEFINITIONS), 'Definition/instance inventory differs')
    return names

def validate_lean(lean, names):
    wanted = {n + '.lean' for n in MODULES} | {'lakefile.lean', 'Check.lean', 'CheckDefinitions.lean'}
    actual_files = set()
    for root, dirs, files in os.walk(lean, followlinks=False):
        parent = Path(root)
        for directory in dirs:
            safe_path(parent / directory)
        if parent == lean:
            dirs[:] = [d for d in dirs if d != '.lake']
        actual_files.update((safe_path(parent / name).relative_to(lean).as_posix() for name in files if name.endswith('.lean')))
    require(actual_files == wanted, 'Unexpected or missing authored Lean module')
    declared = []
    per_module = {}
    forbidden = '\\b(?:sorry|sorryAx|admit|axiom|native_decide|unsafe|implemented_by|extern|run_tac|elab|macro|initialize|opaque)\\b'
    for module, namespace in MODULES.items():
        raw = safe_path(lean / (module + '.lean')).read_bytes()
        require(sha256(raw) == MATH_HASHES[module], 'Frozen mathematical/diagnostic source raw hash mismatch: ' + module)
        text = raw.decode('utf-8', errors='strict')
        code = scrub_comments(text)
        require(not re.search(forbidden, code), 'Forbidden authored token: ' + module)
        require(re.findall('^namespace\\s+(\\S+)', code, re.M) == [namespace], 'Unexpected source namespace')
        declarations = [namespace + '.' + n for n in re.findall('^(?:@\\[[^\\n]*?\\]\\s*)*(?:theorem|lemma)\\s+(' + NAME + ')', code, re.M)]
        declared.extend(declarations)
        per_module[module] = declarations
    require(Counter(declared) == Counter(names) and len(set(declared)) == 68, 'Exact reviewed public declaration inventory mismatch')
    for file, inventory in (('Check.lean', THEOREMS), ('CheckDefinitions.lean', DEFINITIONS)):
        require(safe_path(lean / file).read_text(encoding='utf-8') == query_source(inventory), 'Additional or missing query command: ' + file)
    return {'count': len(names), 'names': names, 'modules': per_module, 'source_hashes': dict(MATH_HASHES), 'definitions': list(DEFINITIONS), 'boundary': 'Exact reviewed bytes plus known declaration syntax; not a general Lean AST or sandbox claim'}

def preflight(package, repo):
    require(__debug__, 'Python optimized mode disables required diagnostic assertions; run without -O/-OO')
    require(not SPEC_PENDING, 'Unmaterialized reproducer specification')
    package, repo = (safe_path(package), safe_path(repo))
    before = frozen_files(package)
    manifest = json.loads(safe_path(package / 'submission.json').read_text(encoding='utf-8-sig'))
    require(manifest.get('id') == CID and manifest.get('solver') == 'idealistichacker' and (manifest.get('verdict') == 'disproved'), 'Submission identity/verdict mismatch')
    require(safe_path(package / '.gitattributes').read_text(encoding='utf-8') == ATTRIBUTES, 'Expected own-package LF/binary attributes required')
    require(sha256(safe_path(package / 'checks.py').read_bytes()) == CHECKS_SHA256, 'Independent checker source differs')
    require(safe_path(package / 'lean4/.gitignore').read_text(encoding='utf-8') == '.lake/\n', 'Build/dependency ignore scope differs')
    source = validate_source(package, repo, manifest)
    lock = validate_config(package / 'lean4')
    inventory = validate_lean(package / 'lean4', theorem_names(manifest))
    require(frozen_files(package) == before, 'Authored files changed during preflight')
    return {'source': source, 'lock': lock, 'theorems': inventory, 'files': before}

def runtime_environment(lean, lake_path):
    code = 'import json,os; keys=' + repr(RUNTIME_KEYS) + '; print(json.dumps({k:os.environ.get(k) for k in keys}))'
    values = json.loads(run([str(lake_path), '--offline', 'env', sys.executable, '-c', code], lean).decode('utf-8'))
    require(set(values) == set(RUNTIME_KEYS) and all((v is None or isinstance(v, str) for v in values.values())), 'Malformed Lake runtime path query')
    env = child_env()
    for key in list(env):
        if key.upper() in RUNTIME_KEYS:
            del env[key]
    env.update({k: v for k, v in values.items() if v is not None})
    expected = {safe_path(lean / '.lake/build/lib/lean'), safe_path(lake_path.parent.parent / 'lib/lean')}
    expected.update((safe_path(lean / '.lake/packages' / name / '.lake/build/lib/lean') for name, *_ in DEPENDENCIES))
    require(bool(values['LEAN_PATH']), 'Lake omitted module lookup paths')
    actual = set()
    for entry in values['LEAN_PATH'].split(os.pathsep):
        require(bool(entry), 'Empty module search-path entry')
        path = Path(entry)
        actual.add(safe_path(path if path.is_absolute() else lean / path))
    require(actual == expected, 'Unexpected or missing portable module lookup path')
    require(safe_path(Path(env['LEAN_SYSROOT'])) == safe_path(lake_path.parent.parent), 'Runtime Lean sysroot does not match installed Lake')
    return env

def regression(package):
    spec = importlib.util.spec_from_file_location('tlmc918_exact_diagnostics', safe_path(package / 'checks.py'))
    checks = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checks)
    result = checks.regression()
    require(result.get('exact_algebra_vectors') == 64, 'Exact C3 diagnostic vector count differs')
    require(result.get('algebra_coordinate_pair_checks') == 12288, 'Coordinate algebra diagnostics incomplete')
    require(result.get('matrix_samples') == 26 and result.get('matrix_coordinate_pair_checks') == 2028, 'Matrix diagnostics incomplete')
    require(result.get('affine_minor') == '1', 'Real affine minor failed')
    require(all((checks.matrix_trace(i, checks.matrix_identity()) == (2, 0) for i in range(3))), 'Matrix trace must be unnormalized')
    require(all((checks.matrix_trace(i, checks.corner(checks.U3)) == checks.ONE for i in range(3))), 'Actual corner compatibility failed')
    return result

def reproduce(package, repo, lake, skip_update):
    global LAKE_BIN
    package, repo = (safe_path(package), safe_path(repo))
    with phase('preflight.before'):
        before = preflight(package, repo)
    lean = package / 'lean4'
    executable = shutil.which(lake)
    require(executable is not None, 'Installed Lake executable not found')
    lake_path = safe_path(Path(executable))
    require(not (lake_path.parent.name == 'bin' and lake_path.parent.parent.name == '.elan'), 'Installed toolchain Lake required; do not use an auto-installing shim')
    LAKE_BIN = lake_path.parent
    dependencies = None
    report = {'id': CID, 'skip_update': skip_update, 'source': before['source'], 'theorems': before['theorems']}
    try:
        with phase('lake.version'):
            version = run([str(lake_path), '--version'], lean).decode('utf-8')
            require(re.fullmatch('Lake version 5\\.0\\.0-src(?:\\+[0-9a-f]+)? \\(Lean version 4\\.33\\.1\\)\\s*', version) is not None, 'Wrong Lake/Lean release')
        if not skip_update:
            with phase('lake.update'):
                run([str(lake_path), 'update'], lean, 900)
        with phase('preflight.before_cleanup'):
            require(preflight(package, repo) == before, 'Frozen inputs changed before cleanup')
        with phase('dependencies.before'):
            dependencies = materialized_dependencies(lean, before['lock'])
        with phase('own_build.cleanup'):
            clean_project_build(lean)
        with phase('own_build.Main'):
            run([str(lake_path), '--offline', '--no-cache', '--wfail', 'build', '+Main'], lean, 900, show_output=True)
        with phase('lake.runtime_paths'):
            env = runtime_environment(lean, lake_path)
        lean_exe = safe_path(lake_path.parent / ('lean.exe' if os.name == 'nt' else 'lean'))
        with phase('lean.version'):
            version = run([str(lean_exe), '--version'], lean, env=env).decode('utf-8')
            require(re.search('\\bversion\\s+4\\.33\\.1(?=,|\\s|\\)|$)', version) is not None, 'Wrong actual Lean release')
        for label, filename, names in (('theorems', 'Check.lean', THEOREMS), ('definitions', 'CheckDefinitions.lean', DEFINITIONS)):
            with phase('audit.' + label):
                text = run([str(lean_exe), '-DwarningAsError=true', filename], lean, 900, True, env).decode('utf-8')
                report[label + '_axioms'] = audit_axioms(text, names)
                report[label + '_types'] = audit_theorem_types(text, names)
        with phase('diagnostics.python'):
            report['regression'] = regression(package)
        with phase('tests.python'):
            run([sys.executable, '-B', '-m', 'unittest', 'discover', '-s', 'tests', '-v'], package, 60, True)
        report['build'] = 'Clean own-project five-module Main closure, all68 theorem and38 definition/instance type/axiom audits, exact bounded C3/M2 diagnostics and tests'
    finally:
        with phase('preflight.after'):
            require(preflight(package, repo) == before, 'Frozen authored files/manifest/source changed')
        if dependencies is not None:
            with phase('dependencies.after'):
                require(materialized_dependencies(lean, before['lock']) == dependencies, 'Exact dependency state changed')
    check_deadline()
    report.update(status='PASS', dependencies=dependencies, frozen_files=before['files'], timings=list(PROFILE_RECORDS), boundaries='Installed toolchain/shared dependency caches remain trust inputs. Not full-dependency clean, bootstrap, Linux, PDF rebuild, final review or upstream acceptance.')
    return report

def main():
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, 'reconfigure'):
            stream.reconfigure(encoding='utf-8', errors='backslashreplace')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', required=True)
    parser.add_argument('--repo', required=True, type=Path)
    parser.add_argument('--skip-update', action='store_true', help='Require existing exact physical dependency checkouts; no update/fetch/cache download')
    parser.add_argument('--preflight-only', action='store_true', help='Static package/source/config audit only; not publication validation')
    parser.add_argument('--timeout-seconds', type=int, default=285, help='Whole reproduction wall-clock budget, default285s within coordinator300s')
    args = parser.parse_args()
    global DEADLINE, PROFILE_RECORDS
    started = time.monotonic()
    DEADLINE = started + args.timeout_seconds
    PROFILE_RECORDS = []
    try:
        if SPEC_PENDING:
            raise ReproductionError('Pending local specification materialization')
        require(args.timeout_seconds > 0, 'Positive timeout required')
        package = Path(__file__).absolute().parent
        if args.preflight_only:
            report = preflight(package, args.repo)
            report.update(status='PREFLIGHT_ONLY', boundaries='No dependency audit, Lean execution, PDF rebuild or final review')
        else:
            report = reproduce(package, args.repo, args.lake, args.skip_update)
        report['duration_ms'] = round((time.monotonic() - started) * 1000)
        print(json.dumps(report, ensure_ascii=True, indent=2))
        return 0
    except (ReproductionError, OSError, ValueError, subprocess.SubprocessError) as exc:
        print('BLOCKED: ' + str(exc), file=sys.stderr, flush=True)
        print('duration_ms: ' + str(round((time.monotonic() - started) * 1000)), file=sys.stderr, flush=True)
        return 2
if __name__ == '__main__':
    raise SystemExit(main())
