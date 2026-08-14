#!/usr/bin/env python3
"""Check completeness and hash links for Phase 4 private provenance.

This check is offline. Canonical URLs and source-material SHA-256 values are
recorded in ignored private custody; the public script verifies their shape and
their links to the frozen public assets and retained PR patch artifacts.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter
from pathlib import Path

from phase4_harness import HarnessFailure, ROOT, schema_validators, validate_document


POLICY_COMMIT = "7b967eb1aaab674bd6aead708d42c4a83e2aca05"
MATHLIB_REPOSITORY = "leanprover-community/mathlib4"
POLICY_REPOSITORY = "leanprover-community/leanprover-community.github.io"
HEX40 = re.compile(r"[0-9a-f]{40}")
HEX64 = re.compile(r"[0-9a-f]{64}")
PR_GROUP = re.compile(r"pr-(\d+)")


class ProvenanceFailure(RuntimeError):
    """A deterministic provenance hard-gate failure."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ProvenanceFailure(message)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def reference_map(document: dict) -> dict[str, list[str]]:
    refs: dict[str, list[str]] = {}
    for reference in document["snapshot_refs"]:
        key, separator, value = reference.partition(":")
        require(separator == ":" and value, f"invalid snapshot ref in {document['case_id']}")
        refs.setdefault(key, []).append(value)
    return refs


def unique_ref(refs: dict[str, list[str]], key: str, case_id: str) -> str:
    values = refs.get(key, [])
    require(len(values) == 1, f"{case_id} requires exactly one {key} ref")
    return values[0]


def public_assets(case_id: str) -> tuple[Path, Path]:
    matches = list((ROOT / "cases").glob(f"*/{case_id}"))
    require(len(matches) == 1, f"public case directory missing or ambiguous: {case_id}")
    return matches[0] / "public.json", matches[0] / "prompt" / "Case.lean"


def validate_hash_links(document: dict, private_root: Path) -> None:
    case_id = document["case_id"]
    refs = reference_map(document)
    public_json, wrapper = public_assets(case_id)
    expected_public = unique_ref(refs, "public_json_sha256", case_id)
    expected_wrapper = unique_ref(refs, "public_wrapper_sha256", case_id)
    source_material = unique_ref(refs, "source_material_sha256", case_id)
    ported_material = unique_ref(refs, "ported_material_sha256", case_id)
    require(HEX64.fullmatch(source_material) is not None,
            f"invalid source-material SHA-256: {case_id}")
    require(HEX64.fullmatch(ported_material) is not None,
            f"invalid ported-material SHA-256: {case_id}")
    require(source_material != ported_material,
            f"pre-port and post-port material hashes must differ: {case_id}")
    require(expected_public == sha256(public_json), f"public JSON hash mismatch: {case_id}")
    require(expected_wrapper == sha256(wrapper), f"public wrapper hash mismatch: {case_id}")
    require(ported_material == expected_wrapper,
            f"post-port material is not the frozen public wrapper: {case_id}")
    unique_ref(refs, "source_file", case_id)
    unique_ref(refs, "source_declaration", case_id)

    if document["source_class"] == "NATURAL_PR":
        patch_hash = unique_ref(refs, "raw_patch_sha256", case_id)
        require(HEX64.fullmatch(patch_hash) is not None, f"invalid patch SHA-256: {case_id}")
        matches = [
            path for path in (private_root / "provenance" / "raw").glob("*.patch")
            if sha256(path) == patch_hash
        ]
        require(len(matches) == 1, f"retained raw patch hash not found uniquely: {case_id}")
        require(unique_ref(refs, "ported_environment", case_id) == "mathlib-v4.30.0",
                f"ported environment drift: {case_id}")


def validate_natural(document: dict) -> None:
    case_id = document["case_id"]
    environment = document["source_environment"]
    require(environment["repository"] == MATHLIB_REPOSITORY,
            f"non-canonical Mathlib repository: {case_id}")
    require(HEX40.fullmatch(environment["base_commit"]) is not None,
            f"invalid base commit: {case_id}")
    merged = environment.get("merged_commit")
    require(isinstance(merged, str) and HEX40.fullmatch(merged) is not None,
            f"invalid merge commit: {case_id}")
    require(environment["lean_toolchain"].startswith("leanprover/lean4:v4."),
            f"original toolchain missing: {case_id}")
    require(document.get("code_license") == "Apache-2.0",
            f"Mathlib source license missing: {case_id}")
    require(document.get("review_comment_usage") not in (None, "NONE"),
            f"review signal usage missing: {case_id}")
    require(document.get("review_comment_license_assumed") is False,
            f"review comment license must not be assumed: {case_id}")

    pr_match = PR_GROUP.fullmatch(document["group_ids"]["source_pr"])
    require(pr_match is not None, f"source PR grouping key malformed: {case_id}")
    pr_number = pr_match.group(1)
    pr_url = f"https://github.com/{MATHLIB_REPOSITORY}/pull/{pr_number}"
    merge_url = f"https://github.com/{MATHLIB_REPOSITORY}/commit/{merged}"
    urls = document["source_urls"]
    require(pr_url in urls, f"canonical PR URL missing: {case_id}")
    require(merge_url in urls, f"canonical merge URL missing: {case_id}")

    outcome = document.get("source_review_outcome")
    require(isinstance(outcome, dict), f"review outcome missing: {case_id}")
    preference = outcome.get("reviewer_preference")
    comment_id = outcome.get("comment_id")
    require(isinstance(preference, str) and preference.strip(),
            f"human review-signal paraphrase missing: {case_id}")
    require(isinstance(comment_id, str) and comment_id.isdigit(),
            f"review comment ID missing: {case_id}")
    require(any(url == f"{pr_url}#discussion_r{comment_id}" for url in urls),
            f"canonical review-comment URL missing: {case_id}")
    require(isinstance(document.get("porting_changes"), list)
            and all(isinstance(item, str) and item.strip()
                    for item in document["porting_changes"]),
            f"porting change inventory missing: {case_id}")


def validate_official(document: dict) -> None:
    case_id = document["case_id"]
    environment = document["source_environment"]
    require(environment["repository"] == POLICY_REPOSITORY,
            f"official-guide repository drift: {case_id}")
    require(environment["base_commit"] == POLICY_COMMIT,
            f"official-guide commit drift: {case_id}")
    require(environment.get("merged_commit") is None,
            f"official-guide merge commit must be null: {case_id}")
    prefix = f"https://github.com/{POLICY_REPOSITORY}/blob/{POLICY_COMMIT}/"
    require(len(document["source_urls"]) == 1
            and document["source_urls"][0].startswith(prefix),
            f"official-guide canonical URL missing: {case_id}")
    require(document.get("review_comment_usage") == "NONE"
            and document.get("source_review_outcome") is None,
            f"official-guide case must not claim PR review evidence: {case_id}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--private-root", type=Path, default=ROOT / "heldout" / "private"
    )
    args = parser.parse_args()
    try:
        manifest = load_json(ROOT / "manifests" / "PILOT_CASES.json")
        expected_ids = set(manifest["primary_case_ids"])
        paths = sorted((args.private_root / "provenance").glob("*.json"))
        documents = [load_json(path) for path in paths]
        require(all(path.stem == document["case_id"]
                    for path, document in zip(paths, documents, strict=True)),
                "provenance file names must equal their case IDs")
        require({document["case_id"] for document in documents} == expected_ids,
                "private provenance must cover the 16 primary cases exactly")
        validator = schema_validators()["private-provenance.schema.json"]
        for path, document in zip(paths, documents, strict=True):
            validate_document(path, validator)
            validate_hash_links(document, args.private_root)
            groups = document["group_ids"]
            require(all(isinstance(groups[key], str) and groups[key].strip()
                        for key in ("source_pr", "theorem_family", "module_family")),
                    f"grouping keys incomplete: {document['case_id']}")
            if document["source_class"] == "NATURAL_PR":
                validate_natural(document)
            elif document["source_class"] == "OFFICIAL_GUIDE_EXAMPLE":
                validate_official(document)
            else:
                raise ProvenanceFailure(
                    f"synthetic primary provenance forbidden: {document['case_id']}"
                )
        counts = Counter(document["source_class"] for document in documents)
        require(counts == Counter({"NATURAL_PR": 14, "OFFICIAL_GUIDE_EXAMPLE": 2}),
                f"source-class distribution drift: {dict(counts)}")
        print(
            "phase4 provenance passed: 16/16 primary cases; "
            "14 NATURAL_PR + 2 OFFICIAL_GUIDE_EXAMPLE; 0 synthetic"
        )
        return 0
    except (
        OSError,
        ValueError,
        KeyError,
        json.JSONDecodeError,
        HarnessFailure,
        ProvenanceFailure,
    ) as exc:
        print(f"phase4 provenance failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
