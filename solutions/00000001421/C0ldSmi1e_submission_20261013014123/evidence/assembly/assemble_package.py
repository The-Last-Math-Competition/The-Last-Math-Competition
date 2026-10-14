#!/usr/bin/env python3
"""Assemble only root-pinned 1421 artifacts; no subprocess, Git, network or build.

Run only after root reviews this source and seals final-inputs.json. All input
gates run before creating a fresh package folder; output checks follow writes.
Failures preserve any partial folder.
"""
from pathlib import Path, PurePosixPath
import datetime
import gzip
import hashlib
import io
import json
import re
import tarfile

R = Path(__file__).resolve().parent
D = R.parent
FROZEN_SHA = "db3effdd39210ad094c0f16e0fba2f19819086aa9cee8a921208b3cf0eb055f0"
ENGINEERING_INDEX_SHA = "32a1c40bc39af7359c4117703410690981b0e13340ee5274aadf4b60ce2b9f05"
ORIGINAL_SHA = "7fefa10d25b135f3e825f57cabc3043c445fd51f1afb38d2a41b026438b6777a"
E = R / "independent-review/engineering"
G = R / "final-public-guard"
TOOLS = D / "verification-tools-v2"
TOOL_NAMES = ("verify.py", "check_audit_graph.py", "test_hardening.py", "templates/ClosureAudit.lean.txt", "PROVENANCE.json")
REPORT_FILES = ("native-compile.json", "build-receipt.json", "build-stdout.txt", "build-stderr.txt", "report.log", "extracted-text.txt", "render-inventory.json", "visual-review.json")
ATTEMPT_NAMES = {"report.tex", "native-compile.json", "build-receipt.json", "build-stdout.txt", "build-stderr.txt", "report.log"}
ROOT_REPORTS = ("definition-reference.json", "frozen-review-manifest.json", "verification-readiness.json", "independent-stock-preparation.json", "root-basic-review.json", "root-config-review.json", "root-walk-mixing-review.json", "root-full-source-preflight.json", "root-phase1-semantic-review.json", "root-final-semantic-review.json", "root-engineering-review.json", "root-selection-review.json", "root-eligibility-review.json", "root-final-public-guard-review.json", "root-final-report-review.json")
REVIEW_GATES = ("root-full-source-preflight.json", "root-final-semantic-review.json", "root-engineering-review.json", "root-final-public-guard-review.json", "root-final-report-review.json", "independent-review/report-review.json", "report/visual-review.json")
FAKE_OLEANS = {
    "preflight-evidence/hardening/packages/mathlib/.lake/build/lib/lean/FreshFixture.olean": b"changed",
    "preflight-evidence/hardening/runtime/lib/lean/Shadow.olean": b"runtime",
    "preflight-evidence/hardening/stock/.lake/build/lib/lean/FreshFixture.olean": b"cache",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()


def sha(path):
    return sha_bytes(path.read_bytes())


def load(path):
    return json.loads(path.read_text())


def relative(name):
    require(isinstance(name, str) and name and "\\" not in name and all(ord(c) >= 32 for c in name), "Invalid path")
    p = PurePosixPath(name)
    require(not p.is_absolute() and str(p) == name and not {".", ".."}.intersection(p.parts), "Noncanonical relative path: " + name)
    return p


def source(base, name):
    require(base.is_relative_to(D) and base.resolve().is_relative_to(D), "Input root escaped workspace")
    p = base / relative(name)
    require(p.is_file() and p.resolve().is_relative_to(base.resolve()), "Missing/escaped input: " + str(p))
    current = p
    while current != D:
        require(not current.is_symlink(), "Symlink input: " + str(current))
        current = current.parent
    return p


def checked(base, name, digest):
    require(isinstance(digest, str) and re.fullmatch(r"[a-f0-9]{64}", digest), "Unsealed hash: " + name)
    p = source(base, name)
    require(sha(p) == digest, "Input hash changed: " + str(p))
    return p


def copy_plan():
    rows = {"clean-author-input/conjecture.md": "conjecture.md", "report/report.tex": "report.tex", "report/report.pdf": "report.pdf", "package-README.md": "README.md", "package-VERIFICATION.md": "VERIFICATION.md"}
    rows.update({name: "evidence/reviews/" + name for name in ROOT_REPORTS})
    rows["frozen-review-manifest.json"] = "evidence/frozen-review-manifest.json"
    rows.update({"expected-pins/" + n: "evidence/expected-pins/" + n for n in ("lean-toolchain", "lake-manifest.json")})
    rows.update({"clean-author-input/" + n: "evidence/clean-author-input/" + n for n in ("RULES.en.md", "RULES.zh.md", "manifest.json")})
    rows.update({"independent-review/" + n: "evidence/reviews/" + n for n in ("phase1-semantic-review.md", "final-source-semantic-review.md", "report-review.json")})
    rows.update({"report/" + n: "evidence/report/" + n for n in REPORT_FILES})
    rows.update({"generic-dependency-build/" + n: "evidence/generic-dependency-build/" + n for n in ("receipt.json", "stdout.log", "stderr.log")})
    rows["auxiliary/exact_regression.py"] = "auxiliary/exact_regression.py"
    rows.update({"auxiliary/" + n: "auxiliary/root-run/" + n for n in ("receipt.json", "results.json", "stdout.log", "stderr.log", "root-review.json")})
    rows.update({"independent-review/engineering/preflight-evidence/" + n: "auxiliary/independent-run/" + n for n in ("exact-regression-command.json", "exact-regression.json", "exact-regression.stdout", "exact-regression.stderr", "auxiliary-review.json")})
    return rows


def archive_inputs(base, index_name, index_hash, count=None):
    index = load(checked(base, index_name, index_hash))
    require(isinstance(index, dict) and (count is None or len(index) == count), "Unexpected archive index count")
    require(index_name not in index, "Archive index must not hash itself")
    for name, digest in index.items():
        checked(base, name, digest)
    return {**index, index_name: index_hash}


def archive_scope(stem, base, members, byte_limit):
    require(sum(source(base, n).stat().st_size for n in members) <= byte_limit, "Evidence archive exceeds bounded input size")
    for name in members:
        p = source(base, name)
        parts = relative(name).parts
        require(not {"project", "__pycache__", ".git"}.intersection(parts), "Private tree in archive")
        if p.suffix in {".olean", ".ilean", ".o", ".a", ".so", ".dylib", ".pyc", ".dll", ".exe", ".obj"} or ".lake" in parts:
            require(stem == "engineering-records" and name in FAKE_OLEANS and p.read_bytes() == FAKE_OLEANS[name], "Compiled artifact/cache in archive")


def preflight(config):
    require(config["status"] == "READY_FOR_ASSEMBLY" and config["root_reviewed_assembler"] is True, "Root sealing/review incomplete")
    require(config["candidate"] == "00000001421" and config["schema"] == 1, "Wrong configuration")
    require(config["assembler_sha256"] == sha(Path(__file__)), "Assembler not pinned by root")
    frozen = load(checked(R, "frozen-review-manifest.json", FROZEN_SHA))
    require(len(frozen["files"]) == 11 and len([n for n in frozen["files"] if n.endswith(".lean")]) == 8, "Frozen source inventory changed")
    for name, digest in frozen["files"].items():
        checked(R / "review-source/lean", name, digest)
    actual = {p.relative_to(R / "review-source/lean").as_posix() for p in (R / "review-source/lean").rglob("*") if p.is_file()}
    require(actual == set(frozen["files"]), "Unexpected frozen source input")
    rows = copy_plan()
    for name in config["report_pages"]:
        require(re.fullmatch(r"inspected-[1-9][0-9]*\.png", name), "Unexpected inspected page name")
        rows["report/" + name] = "evidence/report/" + name
    attempts = config["report_attempt_files"]
    for name in attempts:
        parts = relative(name).parts
        require(len(parts) == 3 and parts[0] == "report" and re.fullmatch(r"attempt-[1-9][0-9]*", parts[1]) and parts[2] in ATTEMPT_NAMES, "Invalid report attempt file")
        rows[name] = "evidence/" + name
    actual_attempts = {p.relative_to(R).as_posix() for folder in (R / "report").glob("attempt-*") for p in folder.iterdir() if p.is_file() and p.name in ATTEMPT_NAMES}
    require(set(attempts) == actual_attempts and any(n.startswith("report/attempt-1/") for n in attempts), "Report attempt receipts omitted")
    require(set(config["candidate_file_hashes"]) == set(rows), "Candidate copy plan differs from sealed hashes")
    for name, digest in config["candidate_file_hashes"].items():
        checked(R, name, digest)
    for name, digest in config["report_pages"].items():
        require(config["candidate_file_hashes"]["report/" + name] == digest, "Page pin mismatch")
    for name, digest in attempts.items():
        require(config["candidate_file_hashes"][name] == digest, "Attempt pin mismatch")
    require(set(config["review_statuses"]) == set(REVIEW_GATES), "Review gate list changed")
    for name, status in config["review_statuses"].items():
        require(isinstance(status, str) and re.fullmatch(r"PASS(?:_[A-Z0-9]+)*", status) and "PENDING" not in status, "Unfinished review status")
        require(load(R / name)["status"] == status, "Review has not passed: " + name)
    tex, pdf = config["candidate_file_hashes"]["report/report.tex"], config["candidate_file_hashes"]["report/report.pdf"]
    report = load(R / "independent-review/report-review.json")
    require(report["report"]["tex_sha256"] == tex and report["report"]["pdf_sha256"] == pdf, "Independent report review is stale")
    require(report["report"]["required_corrections_remaining"] == [] and report["package_documentation"]["both_documents_read_in_full"] is True, "Report/documentation review incomplete")
    require(report["package_documentation"]["readme_sha256"] == sha(R / "package-README.md"), "README not independently reviewed")
    require(report["package_documentation"]["verification_sha256"] == sha(R / "package-VERIFICATION.md"), "VERIFICATION not independently reviewed")
    root_report = load(R / "root-final-report-review.json")
    require(root_report["independent_report_review_sha256"] == sha(R / "independent-review/report-review.json"), "Root report review is stale")
    require(root_report["tex_sha256"] == tex and root_report["pdf_sha256"] == pdf and root_report["remaining_corrections"] == [], "Root report gate incomplete")
    require(root_report["readme_sha256"] == sha(R / "package-README.md") and root_report["verification_sha256"] == sha(R / "package-VERIFICATION.md"), "Root documentation review is stale")
    visual = load(R / "report/visual-review.json")
    require(visual["tex_sha256"] == tex and visual["pdf_sha256"] == pdf, "Visual review is stale")
    require(root_report["root_visual_review_sha256"] == sha(R / "report/visual-review.json"), "Root visual review binding is stale")
    pages = {"inspected-" + n + ".png": h for n, h in visual["pages"].items()}
    require(pages == config["report_pages"] and len(pages) == visual["page_count"] == config["rendered_page_count"] == 12, "Inspected page coverage mismatch")
    require(visual["pages_actually_viewed"] == list(range(1, 13)) and set(visual["pages"]) == {str(n) for n in range(1, 13)}, "All pages not inspected")
    render = load(R / "report/render-inventory.json")
    require(render["tex_sha256"] == tex and render["pdf_sha256"] == pdf and render["page_count"] == 12 and render["pages"] == visual["pages"], "Render inventory differs")
    require(visual["extracted_text_sha256"] == render["extracted_text_sha256"] == sha(R / "report/extracted-text.txt"), "Extracted text changed")
    native, build = load(R / "report/native-compile.json"), load(R / "report/build-receipt.json")
    require(native["status"] == "SUCCESS" and native["tex_sha256"] == tex, "Native compilation gate failed")
    require(build["exit_code"] == 0 and build["source_unchanged"] and build["tex_sha256"] == tex and build["pdf_sha256"] == pdf, "PDF export gate failed")
    require(build["stdout_sha256"] == sha(R / "report/build-stdout.txt") and build["stderr_sha256"] == sha(R / "report/build-stderr.txt"), "PDF build logs changed")
    require(sha(R / "clean-author-input/conjecture.md") == ORIGINAL_SHA, "Original changed")
    for name in ("lean-toolchain", "lake-manifest.json"):
        require(sha(R / "expected-pins" / name) == frozen["files"][name], "Expected pin changed")
    ready = load(R / "verification-readiness.json")
    require(set(config["verification_tool_hashes"]) == set(TOOL_NAMES), "Tool copy scope changed")
    for name, digest in config["verification_tool_hashes"].items():
        checked(TOOLS, name, digest)
        if name != "PROVENANCE.json":
            require(ready["verified_tool_hashes"][name] == digest, "Unreviewed verification tool")
    engineering = archive_inputs(E, "review-evidence-sha256.json", ENGINEERING_INDEX_SHA, 272)
    root_eng = load(R / "root-engineering-review.json")
    require(root_eng["engineering_verdict_sha256"] == sha(E / "engineering-verdict.json") and root_eng["evidence_index_sha256"] == ENGINEERING_INDEX_SHA, "Root engineering review is stale")
    require(load(E / "engineering-verdict.json")["status"] == "PASS_INDEPENDENT_ENGINEERING_REVIEW", "Engineering verdict failed")
    require(load(E / "summary.json")["status"] == "PASS_PENDING_RUNTIME_HELPER_CLASSIFICATION", "Raw engineering status was rewritten")
    require(load(E / "runtime-helper-classification.json")["status"] == "PASS_EXPLICIT_RUNTIME_HELPER_CLASSIFICATION", "Runtime helpers unclassified")
    for name in ("root-full-source-preflight.json", "root-final-semantic-review.json"):
        require(load(R / name)["manifest_sha256"] == FROZEN_SHA, "Source review is stale")
    require(load(R / "root-final-semantic-review.json")["independent_review_sha256"] == sha(R / "independent-review/final-source-semantic-review.md"), "Independent semantics review changed")
    public = archive_inputs(G, "handoff-SHA256SUMS.json", config["public_guard_index_sha256"])
    guard_actual = {p.relative_to(G).as_posix() for p in G.rglob("*") if p.is_file() and "__pycache__" not in p.parts}
    require(set(public) == guard_actual, "Public guard archive is not the full sealed record set")
    handoff, root_guard = load(G / "handoff.json"), load(R / "root-final-public-guard-review.json")
    require(handoff["public_eligibility_passed_by_root"] is True and handoff["root_decision"]["sha256"] == sha(R / "root-final-public-guard-review.json"), "Public guard handoff not bound to root decision")
    require(root_guard["validation_sha256"] == sha(G / "validation/validation.json"), "Public validation changed")
    require(load(G / "validation/validation.json")["status"] == "PASS_FINAL_PUBLIC_GUARD_METADATA_VALIDATION", "Public validation failed")
    require(sha(G / "ORIGINAL.md") == ORIGINAL_SHA, "Public original bytes differ")
    author = config["author_record_hashes"]
    require(set(author) == {"source-freeze.json", "strict-replay.json", "definitions-map.json"}, "Author record scope changed")
    for name, digest in author.items():
        checked(R / "author", name, digest)
    require(load(R / "author/source-freeze.json")["files"] == frozen["files"], "Author freeze differs")
    require(load(R / "author/strict-replay.json")["files"] == frozen["files"], "Author replay differs")
    require(config["input_plan_sha256"] == sha(R / "assembly-input-plan.json"), "Input plan not sealed")
    archive_scope("engineering-records", E, engineering, 300 * 1024**2)
    archive_scope("public-guard-records", G, public, 32 * 1024**2)
    archive_scope("author-records", R / "author", author, 2 * 1024**2)
    return frozen, rows, engineering, public, author


def main():
    config_bytes = source(R, "final-inputs.json").read_bytes()
    config = json.loads(config_bytes)
    assembly_pins = {"assemble_package.py": config["assembler_sha256"], "assembly-input-plan.json": config["input_plan_sha256"], "final-inputs.json": sha_bytes(config_bytes)}
    frozen, rows, engineering, public, author = preflight(config)
    now = datetime.datetime.now(datetime.timezone.utc)
    parent = R / "package"
    require(not parent.is_symlink(), "Output parent is a symlink")
    package = parent / ("C0ldSmi1e_submission_" + now.strftime("%Y%m%d%H%M%S"))
    package.mkdir(parents=True, exist_ok=False)
    copied, archives = [], []

    def write(target, data):
        p = package / relative(target)
        require(not p.exists() and p.resolve().is_relative_to(package.resolve()), "Output collision/escape")
        p.parent.mkdir(parents=True, exist_ok=True)
        with p.open("xb") as stream:
            stream.write(data)
        return p

    def save(target, value):
        return write(target, (json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n").encode())

    def copy(base, name, target, digest):
        data = checked(base, name, digest).read_bytes()
        require(sha_bytes(data) == digest, "Source changed during copy")
        require(not target.endswith(".lean") or target.startswith("lean/"), "Loose Lean source outside proof tree")
        p = write(target, data)
        require(sha(p) == digest, "Copy hash mismatch")
        copied.append({"source": str(base.relative_to(D) / name), "path": target, "sha256": digest, "size": len(data)})

    for name, digest in sorted(frozen["files"].items()):
        copy(R / "review-source/lean", name, "lean/" + name, digest)
    for name, target in sorted(rows.items()):
        copy(R, name, target, config["candidate_file_hashes"][name])
    copy(R, "clean-author-input/conjecture.md", "evidence/clean-author-input/conjecture.md", ORIGINAL_SHA)
    for name, digest in sorted(config["verification_tool_hashes"].items()):
        copy(TOOLS, name, "verification-tools-v2/" + name, digest)
    for name in ("assemble_package.py", "assembly-input-plan.json", "final-inputs.json"):
        copy(R, name, "evidence/assembly/" + name, assembly_pins[name])

    def archive(stem, base, members, byte_limit):
        archive_scope(stem, base, members, byte_limit)
        dest = package / "evidence" / (stem + ".tar.gz")
        manifest = []
        with dest.open("xb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0, compresslevel=9) as zipped:
            with tarfile.open(fileobj=zipped, mode="w", format=tarfile.USTAR_FORMAT) as tar:
                for name, digest in sorted(members.items()):
                    p = checked(base, name, digest)
                    data = p.read_bytes()
                    require(sha_bytes(data) == digest, "Archive source changed")
                    member = stem + "/" + name
                    info = tarfile.TarInfo(member)
                    info.size, info.mtime, info.mode = len(data), 0, 0o644
                    info.uid = info.gid = 0
                    info.uname = info.gname = ""
                    tar.addfile(info, io.BytesIO(data))
                    manifest.append({"path": member, "sha256": digest, "size": len(data)})
        with tarfile.open(dest, "r:gz") as tar:
            actual = tar.getmembers()
            require([m.name for m in actual] == [m["path"] for m in manifest], "Archive member set/order changed")
            for member, record in zip(actual, manifest):
                require(member.isfile() and member.mtime == 0 and member.mode == 0o644 and member.uid == member.gid == 0 and member.uname == member.gname == "", "Archive metadata not normalized")
                data = tar.extractfile(member).read()
                require(len(data) == record["size"] and sha_bytes(data) == record["sha256"], "Archive member verification failed")
        save("evidence/" + stem + "-manifest.json", {"format": "Sorted USTAR ordinary files, normalized metadata, gzip mtime 0 and blank filename", "member_count": len(manifest), "files": manifest})
        archives.append({"path": dest.relative_to(package).as_posix(), "sha256": sha(dest), "members": len(manifest), "size": dest.stat().st_size})

    archive("engineering-records", E, engineering, 300 * 1024**2)
    archive("public-guard-records", G, public, 32 * 1024**2)
    archive("author-records", R / "author", author, 2 * 1024**2)
    require(sha(package / "conjecture.md") == ORIGINAL_SHA, "Packaged original changed")
    require({p.relative_to(package / "lean").as_posix(): sha(p) for p in (package / "lean").rglob("*") if p.is_file()} == frozen["files"], "Packaged proof tree changed")
    inventory = [{"path": p.relative_to(package).as_posix(), "size": p.stat().st_size, "sha256": sha(p)} for p in sorted(package.rglob("*")) if p.is_file()]
    require(sum(r["size"] for r in inventory) <= 128 * 1024**2, "Packaged artifacts exceed bounded size")
    preparation = {"status": "ASSEMBLED_PENDING_FINAL_PACKAGE_REVIEW", "candidate": "00000001421", "assembled_at": now.isoformat(), "package_name": package.name, "assembly_script_sha256": assembly_pins["assemble_package.py"], "final_inputs_sha256": assembly_pins["final-inputs.json"], "frozen_manifest_sha256": FROZEN_SHA, "copied_inputs": copied, "archives": archives, "content_inventory": inventory, "inventory_excludes": ["package-preparation.json", "SHA256SUMS"], "intentional_test_payloads": {n: b.decode() for n, b in FAKE_OLEANS.items()}, "trust_limits": load(E / "engineering-verdict.json")["trust_limits"], "generic_tool_edge_cases": load(E / "generic-tool-review.json")["generic_edge_cases"], "scope": "Only fresh personal submission files written; no source edits, Git, network, subprocess or build. Archives preserve raw statuses and intentional negative-test records.", "remaining_gates": ["Independent complete assembled-package review", "Any later publication and exact repository scope/remote checks"]}
    save("package-preparation.json", preparation)
    files = sorted(p for p in package.rglob("*") if p.is_file())
    sums = "".join(sha(p) + "  " + p.relative_to(package).as_posix() + "\n" for p in files)
    write("SHA256SUMS", sums.encode())
    require(all(not p.is_symlink() for p in package.rglob("*")), "Linked package output")
    for line in sums.splitlines():
        digest, name = line.split("  ", 1)
        require(sha(package / name) == digest, "Final package checksum mismatch")
    print(json.dumps({"status": preparation["status"], "package": str(package), "file_count": len(files) + 1, "sha256sums_sha256": sha(package / "SHA256SUMS"), "archives": archives}, indent=2))


if __name__ == "__main__":
    main()
