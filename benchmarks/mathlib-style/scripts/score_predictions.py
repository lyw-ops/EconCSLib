#!/usr/bin/env python3
"""Deterministic task-aware scorer for Mathlib Style Benchmark predictions."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any

from phase4_harness import (
    HarnessFailure,
    ROOT,
    load_json,
    require,
    schema_validators,
    validate_document,
)


def span_similarity(left: dict[str, Any], right: dict[str, Any]) -> float:
    if left["artifact"] != right["artifact"]:
        return 0.0
    if left.get("declaration_name") and right.get("declaration_name"):
        if left["declaration_name"] != right["declaration_name"]:
            return 0.0
    left_start, left_end = left["start"]["line"], left["end"]["line"]
    right_start, right_end = right["start"]["line"], right["end"]["line"]
    intersection = max(0, min(left_end, right_end) - max(left_start, right_start) + 1)
    union = max(left_end, right_end) - min(left_start, right_start) + 1
    if intersection == 0:
        return 0.0
    line_score = intersection / union
    if left_start == left_end == right_start == right_end:
        lc1, lc2 = left["start"]["column"], left["end"]["column"]
        rc1, rc2 = right["start"]["column"], right["end"]["column"]
        column_intersection = max(0, min(lc2, rc2) - max(lc1, rc1) + 1)
        column_union = max(lc2, rc2) - min(lc1, rc1) + 1
        line_score *= column_intersection / column_union if column_intersection else 0.0
    return line_score


def finding_similarity(predicted: dict[str, Any], gold: dict[str, Any]) -> float:
    if predicted["rule_id"] != gold["rule_id"]:
        return 0.0
    return span_similarity(predicted["span"], gold["span"])


def finding_metrics(predicted: list[dict[str, Any]], gold: list[dict[str, Any]]) -> dict[str, Any]:
    if not gold:
        perfect = 1.0 if not predicted else 0.0
        return {
            "precision": perfect,
            "recall": 1.0,
            "f1": perfect,
            "priority_accuracy": 1.0 if not predicted else 0.0,
            "matched_predictions": 0,
            "unmatched_predictions": len(predicted),
        }
    if not predicted:
        return {
            "precision": 1.0,
            "recall": 0.0,
            "f1": 0.0,
            "priority_accuracy": 0.0,
            "matched_predictions": 0,
            "unmatched_predictions": 0,
        }
    candidates: list[tuple[float, int, int]] = []
    for pi, prediction in enumerate(predicted):
        for gi, target in enumerate(gold):
            similarity = finding_similarity(prediction, target)
            if similarity:
                predicted_weight = 1.0 if prediction["role"] == "primary" else 0.5
                gold_weight = 1.0 if target["role"] == "primary" else 0.5
                weight = min(predicted_weight, gold_weight)
                candidates.append((similarity * weight, pi, gi))
    matched_pred: set[int] = set()
    matched_gold: set[int] = set()
    matched_pairs: list[tuple[int, int]] = []
    credit = 0.0
    for value, pi, gi in sorted(candidates, reverse=True):
        if pi not in matched_pred and gi not in matched_gold:
            matched_pred.add(pi)
            matched_gold.add(gi)
            matched_pairs.append((pi, gi))
            credit += value
    gold_weight = sum(1.0 if finding["role"] == "primary" else 0.5 for finding in gold)
    predicted_weight = sum(
        1.0 if finding["role"] == "primary" else 0.5 for finding in predicted
    )
    precision = credit / predicted_weight
    recall = credit / gold_weight
    f1 = 0.0 if precision + recall == 0 else 2 * precision * recall / (precision + recall)
    priority_accuracy = (
        sum(predicted[pi]["review_priority"] == gold[gi]["review_priority"]
            for pi, gi in matched_pairs) / len(matched_pairs)
        if matched_pairs else 0.0
    )
    return {
        "precision": precision,
        "recall": recall,
        "f1": f1,
        "priority_accuracy": priority_accuracy,
        "matched_predictions": len(matched_pred),
        "unmatched_predictions": len(predicted) - len(matched_pred),
    }


def findings_f1(predicted: list[dict[str, Any]], gold: list[dict[str, Any]]) -> float:
    """Compatibility helper used by focused unit tests."""
    return finding_metrics(predicted, gold)["f1"]


def answerability_score(prediction: dict[str, Any], gold: dict[str, Any]) -> float:
    return float(prediction["answerability"] == gold["answerability"])


def score_one(
    prediction: dict[str, Any],
    gold: dict[str, Any],
    repair_evaluation: dict[str, Any] | None = None,
) -> dict[str, Any]:
    task = gold["task"]
    require(prediction["case_id"] == gold["case_id"], "prediction/gold case ID mismatch")
    require(prediction["task"] == task, "prediction/gold task mismatch")
    answerability = answerability_score(prediction, gold)
    finding_result = finding_metrics(prediction["findings"], gold["findings"])
    findings = finding_result["f1"]
    if task == "PAIR":
        verdict = float(prediction["verdict"] == gold["verdict"])
        accepted_set = float(prediction["verdict"] in gold["accepted_verdicts"])
        total = 0.25 * answerability + 0.55 * accepted_set + 0.20 * findings
        components = {
            "answerability": answerability,
            "verdict_accuracy": verdict,
            "accepted_set_accuracy": accepted_set,
            "findings_f1": findings,
        }
    elif task == "DETECT":
        total = 0.30 * answerability + 0.70 * findings
        components = {"answerability": answerability, "findings_f1": findings}
    elif task == "REPAIR":
        if gold["answerability"] == "INSUFFICIENT_CONTEXT":
            repair = float(prediction["repaired_code"] == "")
            repair_details: dict[str, Any] = {"insufficient_context_abstention": bool(repair)}
        else:
            require(repair_evaluation is not None,
                    f"missing executable REPAIR evaluation for {gold['case_id']}")
            candidate_hash = hashlib.sha256(prediction["repaired_code"].encode()).hexdigest()
            require(
                repair_evaluation.get("candidate_sha256") == candidate_hash,
                f"REPAIR evaluation hash mismatch for {gold['case_id']}",
            )
            repair = float(repair_evaluation.get("accepted") is True)
            repair_details = {
                "gates": repair_evaluation.get("gates", {}),
                "edit_cost": repair_evaluation.get("edit_cost"),
                "reference_text_match_diagnostic_only": repair_evaluation.get(
                    "reference_text_match_diagnostic_only"
                ),
            }
        total = 0.20 * answerability + 0.25 * findings + 0.55 * repair
        components = {
            "answerability": answerability,
            "findings_f1": findings,
            "repair_gate": repair,
            **repair_details,
        }
    elif task == "LOCATE":
        predicted_locations = set(prediction["location_ids"])
        accepted = set(gold["accepted_location_ids"])
        if not accepted:
            location = float(not predicted_locations)
        elif not predicted_locations:
            location = 0.0
        else:
            overlap = len(predicted_locations & accepted)
            precision = overlap / len(predicted_locations)
            recall = overlap / len(accepted)
            location = 0.0 if precision + recall == 0 else 2 * precision * recall / (precision + recall)
            if predicted_locations & set(gold["preferred_location_ids"]):
                location = min(1.0, location + 0.10)
        total = 0.25 * answerability + 0.20 * findings + 0.55 * location
        components = {"answerability": answerability, "findings_f1": findings, "location": location}
    else:
        raise HarnessFailure(f"unknown task: {task}")
    return {
        "case_id": gold["case_id"],
        "task": task,
        "score": round(total, 6),
        "components": components,
        "finding_metrics": {
            key: round(value, 6) if isinstance(value, float) else value
            for key, value in finding_result.items()
        },
    }


def load_predictions(path: Path, validator: Any) -> dict[str, dict[str, Any]]:
    paths = sorted(path.glob("*.json")) if path.is_dir() else [path]
    result: dict[str, dict[str, Any]] = {}
    for candidate in paths:
        raw = load_json(candidate)
        documents = raw if isinstance(raw, list) else [raw]
        for document in documents:
            errors = sorted(validator.iter_errors(document), key=lambda error: list(error.path))
            if errors:
                details = "; ".join(f"{error.json_path}: {error.message}" for error in errors)
                raise HarnessFailure(f"invalid prediction in {candidate}: {details}")
            legacy_aliases = set(load_json(ROOT / "manifests" / "RULES.json")["legacy_aliases"])
            require(
                not ({finding["rule_id"] for finding in document["findings"]} & legacy_aliases),
                f"prediction uses legacy rule alias: {document['case_id']}",
            )
            require(document["case_id"] not in result, f"duplicate prediction: {document['case_id']}")
            result[document["case_id"]] = document
    return result


def load_gold(path: Path, validator: Any) -> dict[str, dict[str, Any]]:
    result: dict[str, dict[str, Any]] = {}
    for candidate in sorted(path.glob("*.json")):
        validate_document(candidate, validator)
        document = load_json(candidate)
        legacy_aliases = set(load_json(ROOT / "manifests" / "RULES.json")["legacy_aliases"])
        require(
            not ({finding["rule_id"] for finding in document["findings"]} & legacy_aliases),
            f"Gold uses legacy rule alias: {document['case_id']}",
        )
        result[document["case_id"]] = document
    return result


def mirror_consistency(predictions: dict[str, dict[str, Any]]) -> dict[str, Any]:
    pairs = load_json(ROOT / "manifests" / "PILOT_CASES.json")["pair_mirrors"]
    checked = stable = 0
    reverse = {"A": "B", "B": "A", "TIE": "TIE", "INSUFFICIENT_CONTEXT": "INSUFFICIENT_CONTEXT"}
    for original, mirror in pairs.items():
        if original not in predictions or mirror not in predictions:
            continue
        checked += 1
        stable += int(reverse[predictions[original]["verdict"]] == predictions[mirror]["verdict"])
    return {"checked": checked, "stable": stable, "rate": None if checked == 0 else stable / checked}


def load_groups(path: Path) -> dict[str, dict[str, str]]:
    groups: dict[str, dict[str, str]] = {}
    manifest = load_json(ROOT / "manifests" / "PILOT_CASES.json")
    stratum_by_case = {
        case_id: stratum
        for stratum, case_ids in manifest["stratum_groups"].items()
        for case_id in case_ids
    }
    for candidate in sorted(path.glob("*.json")):
        document = load_json(candidate)
        case_id = document["case_id"]
        public_paths = list((ROOT / "cases").glob(f"*/{case_id}/public.json"))
        require(len(public_paths) == 1, f"missing public metadata for {case_id}")
        public = load_json(public_paths[0])
        groups[case_id] = {
            **document["group_ids"],
            "task": public["task"],
            "stratum": stratum_by_case[case_id],
            "source_class": document["source_class"],
            "evaluation_mode": public["evaluation_mode"],
        }
    mirrors = manifest["pair_mirrors"]
    for original, mirror in mirrors.items():
        if original in groups:
            groups[mirror] = groups[original]
    return groups


def group_breakdowns(rows: list[dict[str, Any]], groups: dict[str, dict[str, str]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for dimension in (
        "task",
        "stratum",
        "source_class",
        "evaluation_mode",
        "source_pr",
        "theorem_family",
        "module_family",
    ):
        buckets: dict[str, list[float]] = defaultdict(list)
        for row in rows:
            if row["case_id"] in groups:
                buckets[groups[row["case_id"]][dimension]].append(row["score"])
        result[dimension] = {
            key: {"count": len(values), "mean": round(sum(values) / len(values), 6)}
            for key, values in sorted(buckets.items())
        }
    return result


def score_all(
    predictions: dict[str, dict[str, Any]],
    gold: dict[str, dict[str, Any]],
    groups: dict[str, dict[str, str]] | None = None,
    repair_evaluations: dict[str, dict[str, Any]] | None = None,
) -> dict[str, Any]:
    require(predictions, "no predictions found")
    require(set(predictions) <= set(gold), f"predictions without gold: {sorted(set(predictions) - set(gold))}")
    rows = [
        score_one(
            predictions[case_id],
            gold[case_id],
            (repair_evaluations or {}).get(case_id),
        )
        for case_id in sorted(predictions)
    ]
    manifest = load_json(ROOT / "manifests" / "PILOT_CASES.json")
    primary_ids = set(manifest["primary_case_ids"])
    primary_rows = [row for row in rows if row["case_id"] in primary_ids]
    require(primary_rows, "no primary predictions found")
    by_task: dict[str, list[float]] = defaultdict(list)
    for row in primary_rows:
        by_task[row["task"]].append(row["score"])
    task_scores = {task: round(sum(values) / len(values), 6) for task, values in sorted(by_task.items())}
    macro = round(sum(task_scores.values()) / len(task_scores), 6)
    micro = round(sum(row["score"] for row in primary_rows) / len(primary_rows), 6)
    answerability = sum(
        predictions[row["case_id"]]["answerability"] == gold[row["case_id"]]["answerability"]
        for row in primary_rows
    ) / len(primary_rows)
    predicted_abstentions = {
        row["case_id"] for row in primary_rows
        if predictions[row["case_id"]]["answerability"] == "INSUFFICIENT_CONTEXT"
    }
    gold_abstentions = {
        row["case_id"] for row in primary_rows
        if gold[row["case_id"]]["answerability"] == "INSUFFICIENT_CONTEXT"
    }
    abstention_tp = len(predicted_abstentions & gold_abstentions)
    abstention_precision = (
        abstention_tp / len(predicted_abstentions) if predicted_abstentions else 1.0
    )
    abstention_recall = abstention_tp / len(gold_abstentions) if gold_abstentions else 1.0
    abstention_f1 = (
        0.0 if abstention_precision + abstention_recall == 0 else
        2 * abstention_precision * abstention_recall /
        (abstention_precision + abstention_recall)
    )
    total_predicted_findings = sum(
        len(predictions[row["case_id"]]["findings"]) for row in primary_rows
    )
    unsupported_findings = sum(
        row["finding_metrics"]["unmatched_predictions"] for row in primary_rows
    )
    return {
        "scorer_version": "0.3.0",
        "primary_case_count": len(primary_rows),
        "evaluated_case_count_including_mirrors": len(rows),
        "macro_task_score": macro,
        "micro_case_score": micro,
        "task_scores": task_scores,
        "global_metrics": {
            "answerability_accuracy": round(answerability, 6),
            "abstention_calibration": {
                "predicted_count": len(predicted_abstentions),
                "gold_count": len(gold_abstentions),
                "true_positive_count": abstention_tp,
                "precision": round(abstention_precision, 6),
                "recall": round(abstention_recall, 6),
                "f1": round(abstention_f1, 6),
            },
            "unsupported_rationale_rate": (
                0.0 if total_predicted_findings == 0
                else round(unsupported_findings / total_predicted_findings, 6)
            ),
            "unsupported_rationale_contract": (
                "A finding rationale is unsupported when its leaf rule plus declaration-aware "
                "span has zero overlap with every accepted Gold finding; no LLM judge is used."
            ),
        },
        "group_breakdowns": group_breakdowns(primary_rows, groups or {}),
        "mirror_consistency": mirror_consistency(predictions),
        "cases": rows,
    }


def load_repair_evaluations(path: Path) -> dict[str, dict[str, Any]]:
    if not path.is_file():
        return {}
    document = load_json(path)
    require(document.get("repair_evaluator_version") == "1.0.0",
            "unsupported repair evaluator record")
    return {result["case_id"]: result for result in document["results"]}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--predictions", type=Path, required=True)
    parser.add_argument("--gold-dir", type=Path, default=ROOT / "heldout" / "private" / "gold")
    parser.add_argument("--output", type=Path)
    parser.add_argument(
        "--provenance-dir",
        type=Path,
        default=ROOT / "heldout" / "private" / "provenance",
    )
    parser.add_argument(
        "--repair-evaluations",
        type=Path,
        default=ROOT / "heldout" / "private" / "scoring" / "repair-evaluations.json",
    )
    args = parser.parse_args()
    try:
        validators = schema_validators()
        predictions = load_predictions(args.predictions, validators["prediction.schema.json"])
        gold = load_gold(args.gold_dir, validators["private-gold.schema.json"])
        repair_evaluations = load_repair_evaluations(args.repair_evaluations)
        report = score_all(
            predictions,
            gold,
            load_groups(args.provenance_dir),
            repair_evaluations,
        )
        rendered = json.dumps(report, ensure_ascii=False, indent=2) + "\n"
        if args.output:
            args.output.write_text(rendered, encoding="utf-8")
        else:
            print(rendered, end="")
        return 0
    except HarnessFailure as exc:
        print(f"scoring failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
