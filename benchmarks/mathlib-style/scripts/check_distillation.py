#!/usr/bin/env python3
"""Validate the distillation layout, registries, evidence, and case metadata."""

from __future__ import annotations

import json
import hashlib
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = ROOT.parents[1]
DOCS_ROOT = REPO_ROOT / "docs" / "research" / "mathlib-style"
EXPECTED_COMMIT = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
EXPECTED_ENVIRONMENT = "MATHLIB-4.30.0"
EXPECTED_POLICY = "MATHLIB-POLICY-2026-08-13"
EXPECTED_ARTIFACT_VERSION = "0.3.1"
EXPECTED_SCHEMA_VERSION = "0.3.0"
EXPECTED_POLICY_COMMIT = "7b967eb1aaab674bd6aead708d42c4a83e2aca05"
EXPECTED_AUDIT_SHA256 = "6de8679ad90d88a48f6ad792ee1fcd54046c10f647c8d8a813c211db772bf48a"

FROZEN_RULE_IDS = (
    "FIL-001", "FIL-002A", "FIL-002B", "FIL-003", "FIL-005", "FIL-006",
    "FIL-007", "FIL-008", "FMT-001", "FMT-002", "FMT-003", "FMT-004",
    "FMT-005", "FMT-006", "FMT-007", "FMT-008", "FMT-009", "FMT-010",
    "FMT-011", "FMT-012", "FMT-013", "FMT-014", "FMT-015", "FMT-016",
    "FMT-017", "FMT-018", "FMT-019", "NAM-001", "NAM-002", "NAM-003",
    "NAM-004", "NAM-005", "NAM-006", "NAM-007", "NAM-008", "NAM-009",
    "NAM-010A", "NAM-010B", "NAM-010C", "DOC-001A", "DOC-001B", "DOC-001C",
    "DOC-002A", "DOC-002B", "DOC-002C", "DOC-002D", "DOC-003", "DOC-004",
    "DOC-005", "DOC-006", "DOC-007", "DOC-008", "STM-001", "STM-002",
    "STM-003", "STM-004", "STM-005", "PRF-001", "PRF-002", "PRF-003",
    "PRF-004", "PRF-005", "PRF-006", "PRF-007", "API-001", "API-002",
    "API-003", "API-004", "API-005", "API-006", "API-007", "LOC-001",
    "LOC-002A", "LOC-002B", "LOC-003",
)

FROZEN_LEGACY_ALIASES = {
    "FIL-002": ["FIL-002A", "FIL-002B"],
    "FIL-004": ["DOC-001A"],
    "DOC-001": ["DOC-001A", "DOC-001B", "DOC-001C"],
    "DOC-002": ["DOC-002A", "DOC-002B", "DOC-002C", "DOC-002D"],
    "NAM-010": ["NAM-010A", "NAM-010B", "NAM-010C"],
    "LOC-002": ["LOC-002A", "LOC-002B"],
}

EXPECTED_POLICY_FILES = {
    "SG": ("templates/contribute/style.md", "4d7dc29a0edb95fd4e4bc40e2907df8670bf5466"),
    "NC": ("templates/contribute/naming.md", "71b7d85e0bd0c00d7938b7b513fde60dc578a4dc"),
    "DOC": ("templates/contribute/doc.md", "b3a3d201601ec80845714de6d48521f7a34387af"),
    "PR": ("templates/contribute/pr-review.md", "b6b59e101151aeff174f6ce8d335240e52bb0002"),
    "CONTRIB": ("templates/contribute/index.md", "513e08d1957f9b1b98b046fab2052f2c4d6d1261"),
}

EXPECTED_MACHINE_FILES = {
    "LIN-INIT": ("Mathlib/Init.lean", "d0760e71b0bf606cd36d82a2ba155bf84ada6790"),
    "LIN-STYLE": ("Mathlib/Tactic/Linter/Style.lean", "28e1aeff5fc333e0f94037f93590d62cd34a2a07"),
    "LIN-HEADER": ("Mathlib/Tactic/Linter/Header.lean", "bb8fff00908e6fe3d08041d7e23cfaf3ee85c64e"),
    "LIN-WS": ("Mathlib/Tactic/Linter/Whitespace.lean", "054bff27fa7fb13ba2187b6ba8d57eb6a14ed9c8"),
    "LIN-EMPTY": ("Mathlib/Tactic/Linter/EmptyLine.lean", "f6d1325c74655dffce099628f6e1786a6cc822c4"),
    "LIN-DOCSTYLE": ("Mathlib/Tactic/Linter/DocString.lean", "8c245f543eba2196ca7b2674d1eaf653c1b22e00"),
    "LIN-UNUSED": ("Mathlib/Tactic/Linter/UnusedTactic.lean", "2704ae66527eaff1538d1df30e14df1ce8531a47"),
    "LIN-MULTI": ("Mathlib/Tactic/Linter/Multigoal.lean", "48f8bf73adc9ff0d87e12db3d8eb87562a9e7bab"),
    "LIN-DEP": ("Mathlib/Tactic/Linter/DeprecatedSyntaxLinter.lean", "aad82013bae39a6b4a1e544c9fe88241c90e31ac"),
    "LIN-TEXT-BASED": ("Mathlib/Tactic/Linter/TextBased.lean", "1e98722a0e092900ec98816f9c162845406c7518"),
    "LIN-UNICODE": ("Mathlib/Tactic/Linter/TextBased/UnicodeLinter.lean", "b4b7a8b9e8c9e3d01209117035eaadb318bdc843"),
    "CI-LEANCHECKER": (".github/workflows/daily.yml", "0e759fe3ec85ffb70a83d1497037b1cbff4ffdde"),
    "MINIMPORTS": ("Mathlib/Tactic/MinImports.lean", "96d4e88a0a62a2afceae3a4aaa2d95bb6a95144a"),
    "LIN-MINIMPORTS": ("Mathlib/Tactic/Linter/MinImports.lean", "ddfbb78c56a2a2f88e3949f011edc5d60a95fc09"),
}

FROZEN_PHASE2_FILES = {
    "evidence/audits/manual_adversarial_audit.md": EXPECTED_AUDIT_SHA256,
    "cases/detect/README.md": "db441fc82a01ff1a3bf24f131524b8bff329867f086ffc9949bf1ed561328970",
    "cases/locate/README.md": "32e2f457d4b117a2ef0372642afa34e13016c255632146eb7dad94aafb31504e",
    "cases/pair/README.md": "bda6b93142b2b29a1a02cb71ffa278975102176351f6d86e3c63d32bb89d9191",
    "cases/repair/README.md": "e638784aae6b743b5d868f9a3623dd5ce63b08814c93d9119f58b72357523d4b",
    "fixtures/negative/neg_lambda_syntax/Case.lean": "e35cd6aa0e9feec35c4c1bf2fb1d757929c7148b417d69bab189eb067e98d7ee",
    "fixtures/negative/neg_lambda_syntax/case.json": "8877c4ca9045fc678791f4af27086403c4837816a2a66f748fe256d548c049bf",
    "fixtures/positive/pos_image_mono/Case.lean": "bc0822d9dc84b97118b9237a1fe68765313530ab1996b2b948fe5bdd9d0bde6c",
    "fixtures/positive/pos_image_mono/case.json": "ba3d144dfaabbe37e06942e3f8c8ac198793d146c2ce9814a7ba676c6e10f4e4",
    "fixtures/repair/rep_dollar_syntax/After.lean": "3d8ad8a4f060de5669547a29ecc1349827ccd9c719ca5a866fee43725e13503b",
    "fixtures/repair/rep_dollar_syntax/Before.lean": "d73eb2e5a5276fa5652eecdaf3340dfca47256e320b9be2defe3d2f03e32337b",
    "fixtures/repair/rep_dollar_syntax/case.json": "796ec7e53fcaf5a205316423375419028bbd189da358ede8a3178bb7d92eb24c",
    "heldout/.gitignore": "aae815b9313ef60fb99d51bec324f3de1cea5256d6bbf58a660578b3e2d5815c",
    "heldout/README.md": "a08ab12a1d2f3cd5c66e794e8bc7993f199976cf8c79a6bd583ebd2c19bde7c0",
}

PHASE3_RULE_EXPECTATIONS = {
    "FIL-003": ("SHOULD", "ASSISTED", ["linter.style.header", "custom.module_import_order"], ["SG", "DOC", "LIN-HEADER"], "no official total order"),
    "FIL-008": ("MUST", "ASSISTED", ["linter.style.header", "human.location_review"], ["LIN-HEADER"], "performance benchmarking"),
    "FMT-005": ("SHOULD", "HUMAN", ["human.statement_review"], ["SG", "LIN-STYLE"], "typed dependent context"),
    "FMT-011": ("SHOULD", "ASSISTED", ["linter.style.emptyLine", "human.layout_review"], ["SG", "LIN-EMPTY"], "incomplete commands"),
    "FMT-012": ("MUST", "ASSISTED", ["linter.style.setOption", "human.layout_review"], ["LIN-STYLE"], "backward.inferInstanceAs.wrap.reuseSubInstances"),
    "FMT-019": ("MUST", "ASSISTED", ["linter.unicodeLinter", "human.layout_review"], ["SG", "LIN-TEXT-BASED", "LIN-UNICODE"], "snapshot-specific"),
    "DOC-001C": ("SHOULD", "HUMAN", ["human.documentation_review"], ["DOC"], "Main definitions"),
    "DOC-002C": ("SHOULD", "HUMAN", ["human.documentation_review"], ["DOC"], "newly introduced explicit"),
    "DOC-004": ("SHOULD", "ASSISTED", ["linter.style.docString", "human.documentation_review"], ["DOC", "LIN-DOCSTYLE"], "checks only mechanical"),
    "DOC-005": ("SHOULD", "ASSISTED", ["custom.doc_link_check", "human.documentation_review"], ["DOC", "PR"], "Set.mem_iUnion₂"),
    "PRF-007": ("MUST", "DETERMINISTIC", ["linter.style.nativeDecide", "checker.leanchecker"], ["LIN-DEP", "CI-LEANCHECKER"], "lake env leanchecker --fresh Mathlib"),
    "API-007": ("SHOULD", "ASSISTED", ["human.api_review"], ["PR"], "to_additive existing"),
    "LOC-002A": ("SHOULD", "ASSISTED", ["command.#min_imports_in", "linter.minImports", "command.#redundant_imports", "human.location_review"], ["PR", "MINIMPORTS", "LIN-MINIMPORTS"], "activation point downward"),
}

CATEGORY_FAMILIES = {
    "naming": {"NAM"},
    "statements": {"FMT", "STM"},
    "api": {"API"},
    "proofs": {"PRF"},
    "documentation": {"DOC"},
    "imports": {"FIL", "LOC"},
}

REQUIRED_PATHS = [
    "AGENTS.md",
    "README.md",
    "cases/pair",
    "cases/detect",
    "cases/repair",
    "cases/locate",
    "fixtures/positive",
    "fixtures/negative",
    "fixtures/repair",
    "heldout",
    "evidence/naming",
    "evidence/statements",
    "evidence/api",
    "evidence/proofs",
    "evidence/documentation",
    "evidence/imports",
    "evidence/counterexamples",
    "evidence/audits",
    "manifests/RULES.json",
    "manifests/SOURCES.json",
    "manifests/VALIDATORS.json",
    "manifests/COVERAGE.json",
    "manifests/mathlib-4.30.md",
    "manifests/schemas/README.md",
    "manifests/schemas/MANIFEST.json",
    "scripts/static_lean_guard.py",
]

REQUIRED_DOC_PATHS = [
    "README.md",
    "MANUAL_EN.md",
    "TAXONOMY.md",
    "DECISIONS.md",
    "VERSION.md",
    "REPOSITORY_INTEGRATION.md",
    "PHASE1_COMPLETION_REPORT.md",
    "PHASE3_COMPLETION_REPORT.md",
    "PHASE4_COMPLETION_REPORT.md",
]

REQUIRED_REPORT_PATHS = [
    "reports/phase4/PILOT_REPORT.md",
    "reports/phase5/READINESS_AUDIT.md",
]

REMOVED_TRANSLATED_PATHS = [
    "docs/research/mathlib-style/MANUAL_ZH.md",
    "docs/research/mathlib-style/REPOSITORY_INTEGRATION_ZH.md",
    "docs/research/mathlib-style/PHASE1_COMPLETION_REPORT_ZH.md",
    "docs/research/mathlib-style/PHASE3_COMPLETION_REPORT_ZH.md",
    "docs/research/mathlib-style/PHASE4_COMPLETION_REPORT_ZH.md",
    "benchmarks/mathlib-style/reports/phase4/PILOT_REPORT_ZH.md",
    "benchmarks/mathlib-style/reports/phase5/READINESS_AUDIT_ZH.md",
]

CASE_REQUIRED_FIELDS = {
    "schema_version",
    "id",
    "kind",
    "task",
    "status",
    "source_class",
    "evaluation_environment_ref",
    "policy_snapshot_ref",
    "compile_files",
    "evaluation_scope",
    "target_rule_ids",
    "expected_validator_ids",
    "warning_policy",
    "expected_warning_files",
    "purpose",
}


class CheckFailure(Exception):
    """Raised for a validation failure with a user-facing message."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CheckFailure(message)


def load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CheckFailure(f"cannot read JSON {path.relative_to(ROOT)}: {exc}") from exc


def git_output(checkout: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(checkout), *args],
        text=True,
        capture_output=True,
        check=False,
    )
    require(result.returncode == 0, result.stderr.strip() or "git command failed")
    return result.stdout.strip()


def locate_mathlib() -> Path | None:
    configured = os.environ.get("MATHLIB_CHECKOUT")
    candidates = [Path(configured)] if configured else []
    candidates.append(REPO_ROOT / ".lake" / "packages" / "mathlib")
    for candidate in candidates:
        if (candidate / ".git").exists() and (candidate / "Mathlib").is_dir():
            return candidate.resolve()
    return None


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_file_pairs(files: dict[str, Any]) -> dict[str, tuple[str, str]]:
    return {
        source_id: (record.get("path"), record.get("git_blob_sha"))
        for source_id, record in files.items()
    }


def parse_manual_rule_rows(text: str, language: str) -> dict[str, tuple[str, ...]]:
    rows: dict[str, tuple[str, ...]] = {}
    for line in text.splitlines():
        if not re.match(r"^\| `(?:FIL|FMT|NAM|DOC|STM|PRF|API|LOC)-", line):
            continue
        cells = [cell.strip() for cell in line.split(" | ")]
        require(len(cells) == 7, f"{language} manual has malformed rule table row: {line}")
        cells[0] = cells[0].removeprefix("| ")
        cells[-1] = cells[-1].removesuffix(" |")
        match = re.fullmatch(r"`([^`]+)`", cells[0])
        require(match is not None, f"{language} manual has malformed rule ID cell")
        rule_id = match.group(1)
        require(rule_id not in rows, f"{language} manual duplicates {rule_id}")
        rows[rule_id] = tuple(cells[1:])
    return rows


def check_phase2_frozen_assets() -> str:
    for relative, expected_sha256 in FROZEN_PHASE2_FILES.items():
        path = ROOT / relative
        require(path.is_file(), f"missing frozen Phase 2 asset: {relative}")
        require(sha256_file(path) == expected_sha256, f"frozen Phase 2 asset changed: {relative}")
    audit = (ROOT / "evidence" / "audits" / "manual_adversarial_audit.md").read_text(
        encoding="utf-8"
    )
    require("v0.3.0" in audit, "Phase 2 audit no longer identifies its v0.3.0 target")
    require("Phase 3" not in audit, "Phase 2 audit was rewritten with Phase 3 material")
    generated = [
        path.relative_to(ROOT)
        for suffix in ("*.olean", "*.ilean")
        for path in ROOT.rglob(suffix)
    ]
    require(not generated, f"generated Lean artifacts under benchmark tree: {generated}")
    return f"{len(FROZEN_PHASE2_FILES)} Phase 2/case/fixture/held-out files hash-verified"


def check_required_paths() -> None:
    for relative in REQUIRED_PATHS:
        require((ROOT / relative).exists(), f"missing required path: {relative}")
    for relative in REQUIRED_DOC_PATHS:
        require(
            (DOCS_ROOT / relative).is_file(),
            f"missing required documentation: docs/research/mathlib-style/{relative}",
        )
    for relative in REQUIRED_REPORT_PATHS:
        require((ROOT / relative).is_file(), f"missing required report: {relative}")
    for relative in REMOVED_TRANSLATED_PATHS:
        require(not (REPO_ROOT / relative).exists(), f"translated asset remains: {relative}")
    require(
        not (REPO_ROOT / "mathlib-style-distillation").exists(),
        "legacy mathlib-style-distillation directory remains after verified migration",
    )


def check_rules_and_manuals() -> tuple[set[str], int]:
    catalog = load_json(ROOT / "manifests" / "RULES.json")
    rules = catalog.get("rules")
    require(isinstance(rules, list), "manifests/RULES.json has no rules array")
    rule_ids = [rule.get("id") for rule in rules]
    require(all(isinstance(rule_id, str) for rule_id in rule_ids), "rule ID is not a string")
    require(len(rule_ids) == 75, f"expected 75 leaf rules, found {len(rule_ids)}")
    require(len(set(rule_ids)) == len(rule_ids), "duplicate leaf rule IDs")
    require(tuple(rule_ids) == FROZEN_RULE_IDS, "frozen 75-rule ID set/order drift")
    require(catalog.get("rule_count") == len(rule_ids), "catalog rule_count mismatch")
    require(
        catalog.get("schema_version") == EXPECTED_SCHEMA_VERSION,
        "rule-catalog schema version drift",
    )
    require(
        catalog.get("version") == EXPECTED_ARTIFACT_VERSION,
        "unexpected rule-catalog artifact version",
    )
    require(
        catalog.get("status") == "phase3-normative-revision-complete",
        "rule-catalog Phase 3 status drift",
    )
    require(catalog.get("legacy_aliases") == FROZEN_LEGACY_ALIASES, "legacy alias drift")
    require(
        catalog.get("leaf_rule_ids_frozen_for_pilot") is True,
        "leaf rule IDs are no longer marked frozen",
    )
    require(
        set(catalog.get("rule_strength_levels", {}))
        == {"MUST", "SHOULD", "PREFER", "CONTEXT"},
        "rule-strength vocabulary drift",
    )
    require(
        set(catalog.get("finding_priority_levels", {}))
        == {"BLOCKING", "SUBSTANTIVE", "MINOR", "INFORMATIONAL"},
        "finding-priority vocabulary drift",
    )
    require(
        all(rule.get("rule_strength") in catalog["rule_strength_levels"] for rule in rules),
        "rule uses an unknown strength",
    )
    task_union = {
        task for rule in rules for task in rule.get("benchmark_tasks", [])
    }
    require(
        task_union == {"PAIR", "DETECT", "REPAIR", "LOCATE"},
        f"benchmark task vocabulary drift: {sorted(task_union)}",
    )
    require(catalog.get("sources_ref") == "SOURCES.json", "rule-catalog source reference drift")
    require(
        catalog.get("validators_ref") == "VALIDATORS.json",
        "rule-catalog validator reference drift",
    )
    require(
        catalog.get("hard_validation_policy", {}).get(
            "require_native_decision_syntax_and_checker_gate"
        ) is True,
        "native-decision syntax/checker hard gate is missing",
    )

    sources = load_json(ROOT / "manifests" / "SOURCES.json")
    require(
        sources.get("registry_version") == EXPECTED_ARTIFACT_VERSION,
        "source-registry version drift",
    )
    environment = sources.get("evaluation_environment", {})
    policy = sources.get("policy_snapshot", {})
    require(environment.get("id") == EXPECTED_ENVIRONMENT, "evaluation environment ID drift")
    require(environment.get("commit") == EXPECTED_COMMIT, "Mathlib commit drift")
    require(policy.get("id") == EXPECTED_POLICY, "policy snapshot ID drift")
    require(
        policy.get("repository") == "leanprover-community/leanprover-community.github.io"
        and policy.get("commit") == EXPECTED_POLICY_COMMIT,
        "policy snapshot identity drift",
    )
    require(environment.get("release_tag") == "v4.30.0", "Mathlib release drift")
    require(
        environment.get("lean_toolchain") == "leanprover/lean4:v4.30.0",
        "Lean toolchain drift",
    )
    require(
        source_file_pairs(policy.get("files", {})) == EXPECTED_POLICY_FILES,
        "policy source path/blob registry drift",
    )
    machine_snapshot = sources.get("machine_source_snapshot", {})
    require(machine_snapshot.get("commit") == EXPECTED_COMMIT, "machine-source commit drift")
    require(
        source_file_pairs(machine_snapshot.get("files", {})) == EXPECTED_MACHINE_FILES,
        "machine source path/blob registry drift",
    )

    validator_registry = load_json(ROOT / "manifests" / "VALIDATORS.json")
    require(
        validator_registry.get("registry_version") == EXPECTED_ARTIFACT_VERSION,
        "validator-registry version drift",
    )
    validator_ids = {
        validator.get("id") for validator in validator_registry.get("validators", [])
    }
    require(None not in validator_ids, "validator registry contains an entry without an ID")
    source_ids = set(policy.get("files", {}))
    source_ids |= set(sources.get("machine_source_snapshot", {}).get("files", {}))
    for validator in validator_registry.get("validators", []):
        require(
            set(validator.get("source_ids", [])) <= source_ids,
            f"{validator['id']} has unknown source IDs",
        )
    for rule in rules:
        require(set(rule.get("sources", [])) <= source_ids, f"{rule['id']} has unknown sources")
        require(
            set(rule.get("automation", {}).get("validator_ids", [])) <= validator_ids,
            f"{rule['id']} has unknown validators",
        )

    validators_by_id = {
        validator["id"]: validator for validator in validator_registry.get("validators", [])
    }
    checker = validators_by_id.get("checker.leanchecker", {})
    require(
        checker.get("invocation_template") == "lake env leanchecker --fresh Mathlib"
        and checker.get("source_ids") == ["CI-LEANCHECKER"]
        and checker.get("deterministic") is True,
        "pinned leanchecker validator contract drift",
    )
    unicode_linter = validators_by_id.get("linter.unicodeLinter", {})
    require(
        unicode_linter.get("invocation_template") == "lake exe lint-style {module}"
        and unicode_linter.get("source_ids") == ["LIN-TEXT-BASED", "LIN-UNICODE"]
        and unicode_linter.get("deterministic") is True,
        "pinned Unicode linter contract drift",
    )
    doc_link = validators_by_id.get("custom.doc_link_check", {})
    require(
        doc_link.get("kind") == "planned_static_check"
        and doc_link.get("invocation_template") is None
        and doc_link.get("implemented_in_smoke_harness") is False
        and doc_link.get("deterministic") is False,
        "planned doc-link validator is overstated",
    )

    coverage = load_json(ROOT / "manifests" / "COVERAGE.json")
    require(
        coverage.get("version") == EXPECTED_ARTIFACT_VERSION,
        "coverage version drift",
    )
    for row in coverage.get("rows", []):
        require(set(row.get("rule_ids", [])) <= set(rule_ids), "coverage has unknown rule IDs")

    english = (DOCS_ROOT / "MANUAL_EN.md").read_text(encoding="utf-8")
    documented = set(re.findall(r"`((?:FIL|FMT|NAM|DOC|STM|PRF|API|LOC)-[0-9]+[A-Z]?)`", english))
    missing = set(rule_ids) - documented
    require(not missing, f"English manual omits leaf rules: {sorted(missing)}")
    require("**Version:** 0.3.1" in english, "English manual version drift")
    compact_english = " ".join(english.split())
    require(
        "`schema_version` and all 11 JSON Schemas remain byte-for-byte frozen at `0.3.0`"
        in compact_english,
        "English manual does not preserve the v0.3.0 schema boundary",
    )

    manual_rows = parse_manual_rule_rows(english, "English")
    require(set(manual_rows) == set(rule_ids), "English manual table is not exactly 75 rules")
    for rule in rules:
        title, strength, evidence, automation, wording, validators = manual_rows[rule["id"]]
        require(title == rule["title"]["en"], f"English title drift for {rule['id']}")
        require(strength == f"`{rule['rule_strength']}`", f"English strength drift for {rule['id']}")
        require(evidence == f"`{rule['evidence_class']}`", f"English evidence drift for {rule['id']}")
        require(automation == f"`{rule['automation']['level']}`", f"English automation drift for {rule['id']}")
        require(wording == rule["rule"]["en"], f"English wording drift for {rule['id']}")
        require(
            re.findall(r"`([^`]+)`", validators)
            == rule["automation"]["validator_ids"],
            f"English validator list drift for {rule['id']}",
        )

    rules_by_id = {rule["id"]: rule for rule in rules}
    require(set(PHASE3_RULE_EXPECTATIONS) == {
        "FIL-003", "FIL-008", "FMT-005", "FMT-011", "FMT-012", "FMT-019",
        "DOC-001C", "DOC-002C", "DOC-004", "DOC-005", "PRF-007", "API-007",
        "LOC-002A",
    }, "Phase 3 expectation set must contain exactly 13 findings")
    for rule_id, expected in PHASE3_RULE_EXPECTATIONS.items():
        strength, automation, validators, expected_sources, wording_anchor = expected
        rule = rules_by_id[rule_id]
        require(rule["rule_strength"] == strength, f"Phase 3 strength drift for {rule_id}")
        require(rule["automation"]["level"] == automation, f"Phase 3 automation drift for {rule_id}")
        require(rule["automation"]["validator_ids"] == validators, f"Phase 3 validators drift for {rule_id}")
        require(rule["sources"] == expected_sources, f"Phase 3 sources drift for {rule_id}")
        require(wording_anchor in rule["rule"]["en"], f"Phase 3 wording regression for {rule_id}")
    agent_guide = (ROOT / "AGENTS.md").read_text(encoding="utf-8")
    require(
        "sole normative style specification" in agent_guide
        and "English-only Mathlib-style assets" in agent_guide,
        "AGENTS.md must keep the distribution English-only and the manual normative",
    )
    docs_readme = (DOCS_ROOT / "README.md").read_text(encoding="utf-8")
    require(
        "Evaluation Mode" in docs_readme
        and "Distillation/Audit Mode" in docs_readme
        and "cannot be used to prove its own" in docs_readme,
        "documentation must distinguish evaluation from audit authority",
    )
    taxonomy = (DOCS_ROOT / "TAXONOMY.md").read_text(encoding="utf-8")
    taxonomy_ids = set(
        re.findall(r"`((?:FIL|FMT|NAM|DOC|STM|PRF|API|LOC)-[0-9]+[A-Z]?)`", taxonomy)
    )
    require(taxonomy_ids == set(rule_ids), "taxonomy does not cover exactly the 75 leaf rules")
    taxonomy_rows = re.findall(
        r"^\| `((?:FIL|FMT|NAM|DOC|STM|PRF|API|LOC)-[0-9]+[A-Z]?)` "
        r"\| ([^|]+) \| `([^`]+)` \| `([^`]+)` \| `([^`]+)` \|$",
        taxonomy,
        flags=re.MULTILINE,
    )
    require(len(taxonomy_rows) == 75, "taxonomy must contain one data row per leaf rule")
    taxonomy_by_id = {row[0]: row[1:] for row in taxonomy_rows}
    require(len(taxonomy_by_id) == 75, "taxonomy contains duplicate rule rows")
    for rule in rules:
        expected = (
            rule["title"]["en"],
            rule["rule_strength"],
            rule["evidence_class"],
            rule["automation"]["level"],
        )
        actual = taxonomy_by_id[rule["id"]]
        require(actual == expected, f"taxonomy metadata drift for {rule['id']}")
    return set(rule_ids), len(rules)


def iter_schema_nodes(node: Any):
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from iter_schema_nodes(value)
    elif isinstance(node, list):
        for value in node:
            yield from iter_schema_nodes(value)


def resolve_json_pointer(document: Any, pointer: str, context: str) -> Any:
    require(pointer.startswith("/"), f"invalid JSON pointer in {context}: #{pointer}")
    current = document
    for raw_part in pointer[1:].split("/"):
        part = raw_part.replace("~1", "/").replace("~0", "~")
        if isinstance(current, dict):
            require(part in current, f"unresolved JSON pointer in {context}: #{pointer}")
            current = current[part]
        elif isinstance(current, list):
            require(part.isdigit(), f"non-numeric array pointer in {context}: #{pointer}")
            index = int(part)
            require(index < len(current), f"array pointer out of range in {context}: #{pointer}")
            current = current[index]
        else:
            raise CheckFailure(f"JSON pointer traverses a scalar in {context}: #{pointer}")
    return current


def check_schema_shape(schema: Any, context: str) -> None:
    require(isinstance(schema, (dict, bool)), f"schema node is not object/boolean: {context}")
    if isinstance(schema, bool):
        return
    if "type" in schema:
        types = schema["type"] if isinstance(schema["type"], list) else [schema["type"]]
        require(
            types
            and all(item in {"null", "boolean", "object", "array", "number", "string", "integer"}
                    for item in types),
            f"invalid type keyword: {context}",
        )
        require(len(types) == len(set(types)), f"duplicate type alternatives: {context}")
    for keyword in ("properties", "$defs"):
        if keyword in schema:
            require(isinstance(schema[keyword], dict), f"{keyword} must be an object: {context}")
            for name, subschema in schema[keyword].items():
                check_schema_shape(subschema, f"{context}/{keyword}/{name}")
    if "required" in schema:
        required = schema["required"]
        require(
            isinstance(required, list)
            and all(isinstance(item, str) for item in required)
            and len(required) == len(set(required)),
            f"invalid required keyword: {context}",
        )
    if "additionalProperties" in schema:
        check_schema_shape(schema["additionalProperties"], f"{context}/additionalProperties")
    if "items" in schema:
        check_schema_shape(schema["items"], f"{context}/items")
    for keyword in ("allOf", "oneOf"):
        if keyword in schema:
            require(
                isinstance(schema[keyword], list) and schema[keyword],
                f"{keyword} must be a nonempty array: {context}",
            )
            for index, subschema in enumerate(schema[keyword]):
                check_schema_shape(subschema, f"{context}/{keyword}/{index}")
    for keyword in ("if", "then", "else"):
        if keyword in schema:
            check_schema_shape(schema[keyword], f"{context}/{keyword}")
    if "enum" in schema:
        require(isinstance(schema["enum"], list) and schema["enum"], f"invalid enum: {context}")
        encoded = [json.dumps(item, sort_keys=True) for item in schema["enum"]]
        require(len(encoded) == len(set(encoded)), f"duplicate enum values: {context}")
    for keyword in ("minItems", "maxItems", "minLength", "maxLength"):
        if keyword in schema:
            require(
                isinstance(schema[keyword], int)
                and not isinstance(schema[keyword], bool)
                and schema[keyword] >= 0,
                f"invalid {keyword}: {context}",
            )
    if "minimum" in schema:
        require(
            isinstance(schema["minimum"], (int, float))
            and not isinstance(schema["minimum"], bool),
            f"invalid minimum: {context}",
        )
    if "pattern" in schema:
        require(isinstance(schema["pattern"], str), f"pattern must be a string: {context}")
        try:
            re.compile(schema["pattern"])
        except re.error as exc:
            raise CheckFailure(f"invalid pattern in {context}: {exc}") from exc
    if "uniqueItems" in schema:
        require(isinstance(schema["uniqueItems"], bool), f"invalid uniqueItems: {context}")
    if "$ref" in schema:
        require(isinstance(schema["$ref"], str), f"$ref must be a string: {context}")


def check_schema_inventory() -> str:
    schema_dir = ROOT / "manifests" / "schemas"
    manifest = load_json(schema_dir / "MANIFEST.json")
    readme = (schema_dir / "README.md").read_text(encoding="utf-8")
    require(
        "complete set of 11" in readme and "copied verbatim" in readme,
        "schema documentation must record complete verbatim recovery",
    )
    require(manifest.get("schema_set_version") == "0.3.0", "schema-set version drift")
    require(
        manifest.get("source_manifest") == "MANIFEST_v0.3.0.json",
        "schema provenance manifest drift",
    )
    entries = manifest.get("files")
    require(isinstance(entries, list), "schema manifest has no files array")
    expected = {entry.get("path"): entry for entry in entries}
    require(None not in expected, "schema manifest entry has no path")
    require(len(expected) == 11 == len(entries), "expected exactly 11 unique v0.3.0 schemas")
    actual = {path.name for path in schema_dir.glob("*.schema.json")}
    require(actual == set(expected), "schema file set does not match frozen manifest")

    documents: dict[str, Any] = {}
    schema_ids: set[str] = set()
    for name, entry in expected.items():
        path = schema_dir / name
        raw = path.read_bytes()
        require(len(raw) == entry.get("bytes"), f"schema byte-count mismatch: {name}")
        require(
            hashlib.sha256(raw).hexdigest() == entry.get("sha256"),
            f"schema SHA-256 mismatch: {name}",
        )
        document = load_json(path)
        require(isinstance(document, dict), f"schema is not a JSON object: {name}")
        require(
            document.get("$schema") == "https://json-schema.org/draft/2020-12/schema",
            f"schema is not Draft 2020-12: {name}",
        )
        schema_id = document.get("$id")
        require(isinstance(schema_id, str) and schema_id.startswith("https://"), f"bad $id: {name}")
        require(schema_id not in schema_ids, f"duplicate schema $id: {schema_id}")
        schema_ids.add(schema_id)
        check_schema_shape(document, name)
        documents[name] = document

    for name, document in documents.items():
        for node in iter_schema_nodes(document):
            reference = node.get("$ref")
            if reference is None:
                continue
            target_name, separator, fragment = reference.partition("#")
            target_name = target_name or name
            require(target_name in documents, f"unresolved local schema reference in {name}: {reference}")
            if separator and fragment:
                target = resolve_json_pointer(documents[target_name], fragment, f"{name}: {reference}")
                require(
                    isinstance(target, (dict, bool)),
                    f"$ref target is not a schema in {name}: {reference}",
                )
    return "11 frozen v0.3.0 schemas hash-verified and reference-checked"


def check_markdown_links() -> None:
    roots = (DOCS_ROOT, ROOT)
    for base in roots:
        for markdown in base.rglob("*.md"):
            text = markdown.read_text(encoding="utf-8")
            for target in re.findall(r"\[[^\]]*\]\(([^)]+)\)", text):
                target = target.split(maxsplit=1)[0].strip("<>")
                if not target or target.startswith(("#", "http://", "https://", "mailto:")):
                    continue
                relative = target.split("#", 1)[0]
                require(
                    (markdown.parent / relative).resolve().exists(),
                    f"broken Markdown link in {markdown.relative_to(REPO_ROOT)}: {target}",
                )


def check_english_only_distribution() -> str:
    text_suffixes = {".json", ".jsonl", ".lean", ".md", ".py", ".txt", ".yaml", ".yml"}
    cjk = re.compile(r"[\u3400-\u4dbf\u4e00-\u9fff\uf900-\ufaff]")
    checked = 0
    for base in (DOCS_ROOT, ROOT):
        for path in base.rglob("*"):
            if not path.is_file() or path.suffix.lower() not in text_suffixes:
                continue
            if ROOT in path.parents:
                relative = path.relative_to(ROOT)
                if relative.parts[:2] == ("heldout", "private"):
                    continue
            text = path.read_text(encoding="utf-8")
            require(
                cjk.search(text) is None,
                f"non-English CJK text remains in {path.relative_to(REPO_ROOT)}",
            )
            checked += 1
    return f"{checked} distributed text files checked as English-only"


def check_category_indexes(rule_ids: set[str]) -> None:
    seen: set[str] = set()
    for category, families in CATEGORY_FAMILIES.items():
        index = load_json(ROOT / "evidence" / category / "INDEX.json")
        indexed = index.get("rule_ids")
        require(isinstance(indexed, list), f"{category}/INDEX.json has no rule_ids array")
        indexed_set = set(indexed)
        expected = {rule_id for rule_id in rule_ids if rule_id.split("-", 1)[0] in families}
        require(indexed_set == expected, f"{category} index does not match its rule families")
        require(index.get("rule_count") == len(indexed), f"{category} rule_count mismatch")
        require(
            index.get("source") == "../../manifests/RULES.json",
            f"{category} rule-catalog path drift",
        )
        overlap = seen & indexed_set
        require(not overlap, f"rules occur in multiple category indexes: {sorted(overlap)}")
        seen |= indexed_set
    require(seen == rule_ids, "category indexes do not partition the leaf rules")


def load_evidence_records(rule_ids: set[str]) -> tuple[list[dict[str, Any]], int]:
    records: list[dict[str, Any]] = []
    seen_ids: set[str] = set()
    required = {
        "id",
        "mathlib_commit",
        "path",
        "blob_sha",
        "line_start",
        "line_end",
        "anchor",
        "rule_ids",
        "assessment",
        "explanation",
    }
    for category in CATEGORY_FAMILIES:
        path = ROOT / "evidence" / category / "EXAMPLES.jsonl"
        require(path.is_file(), f"missing evidence examples: {category}/EXAMPLES.jsonl")
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            if not line.strip():
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError as exc:
                raise CheckFailure(f"invalid JSONL at {path.relative_to(ROOT)}:{number}: {exc}") from exc
            missing = required - record.keys()
            require(not missing, f"{record.get('id', path.name)} missing fields: {sorted(missing)}")
            require(record["id"] not in seen_ids, f"duplicate evidence ID: {record['id']}")
            seen_ids.add(record["id"])
            require(record["mathlib_commit"] == EXPECTED_COMMIT, f"{record['id']} commit drift")
            require(set(record["rule_ids"]) <= rule_ids, f"{record['id']} has unknown rule IDs")
            require(
                isinstance(record["line_start"], int)
                and isinstance(record["line_end"], int)
                and 1 <= record["line_start"] <= record["line_end"],
                f"{record['id']} has an invalid line range",
            )
            records.append(record)
    return records, len(seen_ids)


def check_evidence_checkout(records: list[dict[str, Any]]) -> str:
    checkout = locate_mathlib()
    if checkout is None:
        return "checkout unavailable; structural evidence checks only"
    actual_commit = git_output(checkout, "rev-parse", "HEAD")
    require(actual_commit == EXPECTED_COMMIT, f"Mathlib checkout is {actual_commit}, not pinned commit")
    for record in records:
        source = checkout / record["path"]
        require(source.is_file(), f"{record['id']} source path is missing: {record['path']}")
        actual_blob = git_output(checkout, "hash-object", record["path"])
        require(actual_blob == record["blob_sha"], f"{record['id']} blob SHA mismatch")
        line_count = sum(1 for _ in source.open(encoding="utf-8"))
        require(record["line_end"] <= line_count, f"{record['id']} range exceeds source length")
    sources = load_json(ROOT / "manifests" / "SOURCES.json")
    machine_files = sources["machine_source_snapshot"]["files"]
    for source_id, record in machine_files.items():
        source = checkout / record["path"]
        require(source.is_file(), f"{source_id} source path is missing: {record['path']}")
        actual_blob = git_output(checkout, "hash-object", record["path"])
        require(actual_blob == record["git_blob_sha"], f"{source_id} source blob SHA mismatch")
    return f"verified evidence and {len(machine_files)} machine sources against {checkout}"


def check_benchmark_metadata(rule_ids: set[str]) -> tuple[int, int]:
    validator_registry = load_json(ROOT / "manifests" / "VALIDATORS.json")
    validator_ids = {
        validator.get("id") for validator in validator_registry.get("validators", [])
    }
    require(None not in validator_ids, "validator registry contains an entry without an ID")
    seen_case_ids: set[str] = set()
    lean_files = 0
    cases = 0
    for kind in ("positive", "negative", "repair"):
        manifests = sorted((ROOT / "fixtures" / kind).glob("*/case.json"))
        require(manifests, f"fixtures/{kind} has no visible smoke case")
        for manifest_path in manifests:
            case = load_json(manifest_path)
            missing = CASE_REQUIRED_FIELDS - case.keys()
            require(not missing, f"{manifest_path.relative_to(ROOT)} missing fields: {sorted(missing)}")
            require(case["id"] not in seen_case_ids, f"duplicate benchmark case ID: {case['id']}")
            seen_case_ids.add(case["id"])
            require(case["kind"] == kind, f"{case['id']} kind/directory mismatch")
            require(case["task"] in {"PAIR", "DETECT", "REPAIR", "LOCATE"}, f"{case['id']} bad task")
            require(case["status"] == "SYNTHETIC_SMOKE", f"{case['id']} overstates benchmark maturity")
            require(case["source_class"] == "SYNTHETIC", f"{case['id']} source-class mismatch")
            require(
                case["evaluation_environment_ref"] == EXPECTED_ENVIRONMENT,
                f"{case['id']} evaluation environment drift",
            )
            require(case["policy_snapshot_ref"] == EXPECTED_POLICY, f"{case['id']} policy drift")
            require(set(case["target_rule_ids"]) <= rule_ids, f"{case['id']} has unknown rules")
            require(
                set(case["expected_validator_ids"]) <= validator_ids,
                f"{case['id']} has unknown validator IDs",
            )
            compile_files = case["compile_files"]
            expected_warning_files = set(case["expected_warning_files"])
            require(isinstance(compile_files, list) and compile_files, f"{case['id']} has no compile files")
            require(expected_warning_files <= set(compile_files), f"{case['id']} warning file not compiled")
            require(
                case["warning_policy"] in {"none", "target_only"},
                f"{case['id']} has an unsupported warning policy",
            )
            if case["warning_policy"] == "none":
                require(not expected_warning_files, f"{case['id']} contradicts warning_policy=none")
            for relative in compile_files:
                source = manifest_path.parent / relative
                require(source.is_file() and source.suffix == ".lean", f"{case['id']} missing {relative}")
                guard = subprocess.run(
                    [sys.executable, str(ROOT / "scripts" / "static_lean_guard.py"), str(source)],
                    text=True,
                    capture_output=True,
                    check=False,
                )
                require(guard.returncode == 0, f"{case['id']} hard guard failed: {guard.stderr.strip()}")
                lean_files += 1
            if kind == "repair":
                require(case["task"] == "REPAIR", f"{case['id']} repair case must use REPAIR task")
                require(
                    (manifest_path.parent / case["reference_repair"]).is_file(),
                    f"{case['id']} reference repair is missing",
                )
            cases += 1

    allowed_heldout = {"README.md", ".gitignore", "private"}
    heldout_entries = {path.name for path in (ROOT / "heldout").iterdir()}
    require(heldout_entries <= allowed_heldout, "heldout directory contains committed-looking data")
    private_root = ROOT / "heldout" / "private"
    if private_root.exists():
        ignored = subprocess.run(
            ["git", "check-ignore", "-q", str(private_root / "sentinel.json")],
            cwd=REPO_ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        require(ignored.returncode == 0, "heldout/private is not ignored by Git")
        tracked = subprocess.run(
            ["git", "ls-files", "--", str(private_root)],
            cwd=REPO_ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        require(
            tracked.returncode == 0 and not tracked.stdout.strip(),
            "heldout/private contains tracked files",
        )
    return cases, lean_files


def main() -> int:
    try:
        check_required_paths()
        frozen_status = check_phase2_frozen_assets()
        rule_ids, rule_count = check_rules_and_manuals()
        check_category_indexes(rule_ids)
        schema_status = check_schema_inventory()
        language_status = check_english_only_distribution()
        check_markdown_links()
        records, evidence_count = load_evidence_records(rule_ids)
        checkout_status = check_evidence_checkout(records)
        case_count, lean_count = check_benchmark_metadata(rule_ids)
    except CheckFailure as exc:
        print(f"distillation check failed: {exc}", file=sys.stderr)
        return 1

    print(
        "distillation check passed: "
        f"{rule_count} rules, {evidence_count} evidence anchors, "
        f"{case_count} smoke cases/{lean_count} Lean files; {checkout_status}; "
        f"{schema_status}; {frozen_status}; {language_status}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
