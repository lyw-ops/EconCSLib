#!/usr/bin/env python3
"""Validate the R000 registry, schemas, prerequisites, and obligation DAGs."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


SCRIPT_ROOT = Path(__file__).resolve().parent
if str(SCRIPT_ROOT) not in sys.path:
    sys.path.insert(0, str(SCRIPT_ROOT))

from rubric_common import R000_PATH, RUBRIC_ROOT, load_json, validate_instance  # noqa: E402


GRAPH_NAMES = ("core", "direct", "transport", "paired")


def _acyclic(nodes: set[str], edges: list[tuple[str, str]]) -> bool:
    outgoing = {node: [] for node in nodes}
    indegree = {node: 0 for node in nodes}
    for source, target in edges:
        outgoing[source].append(target)
        indegree[target] += 1
    ready = sorted(node for node, degree in indegree.items() if degree == 0)
    visited = 0
    while ready:
        node = ready.pop(0)
        visited += 1
        for target in sorted(outgoing[node]):
            indegree[target] -= 1
            if indegree[target] == 0:
                ready.append(target)
                ready.sort()
    return visited == len(nodes)


def validate_rubric(rubric_path: Path = R000_PATH) -> dict[str, Any]:
    errors: list[str] = []
    rubric = load_json(rubric_path)
    schemas = {
        name: load_json(RUBRIC_ROOT / "schemas" / f"{name}.schema.json")
        for name in ("rubric", "criterion", "obligation-result", "shadow-evaluation")
    }
    errors.extend(validate_instance(rubric, schemas["rubric"], "$rubric"))
    for index, criterion in enumerate(rubric.get("criteria", [])):
        errors.extend(validate_instance(
            criterion, schemas["criterion"], f"$rubric.criteria[{index}]"
        ))

    criteria = rubric.get("criteria", [])
    criterion_ids = [item.get("criterion_id") for item in criteria if isinstance(item, dict)]
    known = set(criterion_ids)
    if len(criterion_ids) != len(known):
        errors.append("criterion IDs are not unique")
    for criterion in criteria:
        for prerequisite in criterion.get("prerequisites", []):
            if prerequisite not in known:
                errors.append(
                    f"{criterion.get('criterion_id')}: unknown prerequisite {prerequisite}"
                )

    registry_edges = [
        (prerequisite, criterion["criterion_id"])
        for criterion in criteria
        for prerequisite in criterion.get("prerequisites", [])
        if prerequisite in known
    ]
    if known and not _acyclic(known, registry_edges):
        errors.append("criterion prerequisite graph contains a cycle")

    graphs = {
        name: load_json(RUBRIC_ROOT / "obligation_graphs" / f"{name}.json")
        for name in GRAPH_NAMES
    }

    def inherited_nodes(name: str, stack: tuple[str, ...] = ()) -> set[str]:
        if name in stack:
            errors.append(f"graph inheritance cycle: {' -> '.join(stack + (name,))}")
            return set()
        graph = graphs[name]
        nodes = set(graph.get("nodes", []))
        for parent in graph.get("inherits", []):
            if parent not in graphs:
                errors.append(f"{name}: unknown inherited graph {parent}")
            else:
                nodes.update(inherited_nodes(parent, stack + (name,)))
        return nodes

    for name, graph in graphs.items():
        nodes = inherited_nodes(name)
        own_nodes = set(graph.get("nodes", []))
        if not own_nodes <= known:
            errors.append(f"{name}: graph has unknown nodes {sorted(own_nodes - known)}")
        edges: list[tuple[str, str]] = []
        for raw_edge in graph.get("edges", []):
            if not isinstance(raw_edge, list) or len(raw_edge) != 2:
                errors.append(f"{name}: malformed edge {raw_edge!r}")
                continue
            edge = (raw_edge[0], raw_edge[1])
            edges.append(edge)
            if edge[0] not in nodes or edge[1] not in nodes:
                errors.append(f"{name}: edge references a node outside its inherited graph: {edge}")
        if nodes and not _acyclic(nodes, edges + [
            edge for edge in registry_edges if edge[0] in nodes and edge[1] in nodes
        ]):
            errors.append(f"{name}: obligation graph contains a cycle")
        edge_set = set(edges)
        for criterion in criteria:
            if criterion["criterion_id"] not in own_nodes:
                continue
            for prerequisite in criterion["prerequisites"]:
                if (prerequisite, criterion["criterion_id"]) not in edge_set:
                    errors.append(
                        f"{name}: missing prerequisite edge {prerequisite} -> {criterion['criterion_id']}"
                    )

    return {
        "status": "passed" if not errors else "failed",
        "rubric_id": rubric.get("rubric_id"),
        "criteria": len(criteria),
        "graphs": len(graphs),
        "errors": errors,
    }


def main() -> int:
    report = validate_rubric()
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
