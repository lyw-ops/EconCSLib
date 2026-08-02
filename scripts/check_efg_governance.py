#!/usr/bin/env python3
"""Check enforceable EFG architecture and lifecycle invariants.

This is intentionally a source-graph check rather than a Lean parser. It
guards the documented module register, import-only compatibility modules,
stable facade closures, root aggregate boundary, and dependency direction.
Lean elaboration and placeholder checks remain separate CI steps.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import re
import sys


IMPORT_RE = re.compile(
    r"^import\s+(EconCSLib(?:\.[A-Za-z0-9_]+)*)\s*$", re.MULTILINE
)
MODULE_ROW_RE = re.compile(r"^\| `(EconCSLib\.[^`]+)` \|", re.MULTILINE)
DECLARATION_RE = re.compile(
    r"^(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+)*"
    r"(?:abbrev|axiom|class|def|example|inductive|instance|lemma|opaque|"
    r"structure|theorem)\b",
    re.MULTILINE,
)
DEPRECATED_RE = re.compile(
    r"@\[\s*deprecated[^\]]*\]\s*"
    r"(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+)*"
    r"(?:abbrev|class|def|inductive|instance|lemma|structure|theorem)\s+"
    r"([A-Za-z0-9_'.]+)",
    re.MULTILINE,
)

EFG_PREFIX = "EconCSLib.GameTheory.ExtensiveGame."

EXPECTED_CLOSURES = {
    "EconCSLib": (37, 165),
    f"{EFG_PREFIX}Interface.StructuralCore": (5, 5),
    f"{EFG_PREFIX}Interface.Core": (14, 14),
    f"{EFG_PREFIX}Interface.Objective": (32, 37),
    f"{EFG_PREFIX}Interface.Winning": (35, 40),
    f"{EFG_PREFIX}Interface.Winning.Stochastic": (50, 57),
    f"{EFG_PREFIX}Interface.Execution.Finite": (33, 40),
    f"{EFG_PREFIX}Interface.Execution.Infinite": (38, 45),
    f"{EFG_PREFIX}Interface.Execution.Analytic": (58, 66),
    f"{EFG_PREFIX}Interface.Relations.Discrete": (39, 46),
    f"{EFG_PREFIX}Interface.Equilibrium.Discrete": (66, 82),
    f"{EFG_PREFIX}Interface.Equilibrium.Analytic": (96, 113),
    f"{EFG_PREFIX}Interface.Restart": (104, 121),
    f"{EFG_PREFIX}Interface.Compilation.Discrete": (87, 105),
}

STRUCTURAL_CORE = f"{EFG_PREFIX}Interface.StructuralCore"
EXPECTED_STRUCTURAL_CORE_EFG_CLOSURE = {
    f"{EFG_PREFIX}Basic",
    f"{EFG_PREFIX}Execution.Reachability",
    f"{EFG_PREFIX}Execution.History",
    f"{EFG_PREFIX}Execution.CompletePlay",
    f"{EFG_PREFIX}Observed.Controlled",
}

CONTROLLED_INFRASTRUCTURE_RECALL = (
    f"{EFG_PREFIX}Observed.ControlledInfrastructure.Recall"
)
CONTROLLED_INFRASTRUCTURE_WELL_FORMED = (
    f"{EFG_PREFIX}Observed.ControlledInfrastructure.WellFormed"
)
CONTROLLED_MORPHISM_CORE = f"{EFG_PREFIX}Observed.ControlledMorphism.Core"
CONTROLLED_MORPHISM_SUBGAME = f"{EFG_PREFIX}Observed.ControlledMorphism.Subgame"
CONTROLLED_MORPHISM_RECALL = f"{EFG_PREFIX}Observed.ControlledMorphism.Recall"

EXPECTED_EXACT_EFG_CLOSURES = {
    CONTROLLED_INFRASTRUCTURE_RECALL: {
        f"{EFG_PREFIX}Basic",
        f"{EFG_PREFIX}Execution.Reachability",
        f"{EFG_PREFIX}Execution.History",
        f"{EFG_PREFIX}Execution.CompletePlay",
        f"{EFG_PREFIX}Observed.Controlled",
        CONTROLLED_INFRASTRUCTURE_WELL_FORMED,
    },
    CONTROLLED_INFRASTRUCTURE_WELL_FORMED: {
        f"{EFG_PREFIX}Basic",
        f"{EFG_PREFIX}Execution.Reachability",
        f"{EFG_PREFIX}Execution.History",
        f"{EFG_PREFIX}Execution.CompletePlay",
        f"{EFG_PREFIX}Observed.Controlled",
    },
    CONTROLLED_MORPHISM_CORE: {
        f"{EFG_PREFIX}Basic",
        f"{EFG_PREFIX}Execution.Reachability",
        f"{EFG_PREFIX}Execution.History",
        f"{EFG_PREFIX}Execution.CompletePlay",
        f"{EFG_PREFIX}Execution.StoppedExecution",
        f"{EFG_PREFIX}Execution.DependentFiber",
        f"{EFG_PREFIX}Relations.Discrete.Morphism",
        f"{EFG_PREFIX}Observed.Controlled",
    },
    CONTROLLED_MORPHISM_SUBGAME: {
        f"{EFG_PREFIX}Basic",
        f"{EFG_PREFIX}Execution.Reachability",
        f"{EFG_PREFIX}Execution.History",
        f"{EFG_PREFIX}Execution.CompletePlay",
        f"{EFG_PREFIX}Execution.StoppedExecution",
        f"{EFG_PREFIX}Execution.DependentFiber",
        f"{EFG_PREFIX}Relations.Discrete.Morphism",
        f"{EFG_PREFIX}Observed.Controlled",
        f"{EFG_PREFIX}Observed.ControlledInfrastructure.Subgame",
        CONTROLLED_MORPHISM_CORE,
    },
    CONTROLLED_MORPHISM_RECALL: {
        f"{EFG_PREFIX}Basic",
        f"{EFG_PREFIX}Execution.Reachability",
        f"{EFG_PREFIX}Execution.History",
        f"{EFG_PREFIX}Execution.CompletePlay",
        f"{EFG_PREFIX}Execution.StoppedExecution",
        f"{EFG_PREFIX}Execution.DependentFiber",
        f"{EFG_PREFIX}Relations.Discrete.Morphism",
        f"{EFG_PREFIX}Observed.Controlled",
        CONTROLLED_INFRASTRUCTURE_WELL_FORMED,
        CONTROLLED_INFRASTRUCTURE_RECALL,
        CONTROLLED_MORPHISM_CORE,
    },
}

EXPECTED_COMPATIBILITY_AGGREGATE_IMPORTS = {
    f"{EFG_PREFIX}Observed.ControlledInfrastructure": {
        f"{EFG_PREFIX}Observed.ControlledInfrastructure.Core",
        CONTROLLED_INFRASTRUCTURE_WELL_FORMED,
        f"{EFG_PREFIX}Observed.ControlledInfrastructure.Subgame",
        f"{EFG_PREFIX}Observed.ControlledInfrastructure.Finite",
        f"{EFG_PREFIX}Observed.ControlledInfrastructure.Quasi",
        f"{EFG_PREFIX}Observed.ControlledInfrastructure.Recall",
        f"{EFG_PREFIX}Winning.Basic",
    },
    f"{EFG_PREFIX}Observed.ControlledMorphism": {
        CONTROLLED_MORPHISM_CORE,
        CONTROLLED_MORPHISM_SUBGAME,
        CONTROLLED_MORPHISM_RECALL,
    },
}

CORE_FORBIDDEN_CLOSURE_MODULES = {
    f"{EFG_PREFIX}Execution.Objective",
    f"{EFG_PREFIX}Winning.Basic",
}

CORE_FORBIDDEN_CLOSURE_PREFIXES = (
    f"{EFG_PREFIX}Winning.",
)

EXPECTED_ROOT_EFG_IMPORTS = {
    f"{EFG_PREFIX}Interface.Execution.Finite",
    f"{EFG_PREFIX}GameTree",
    f"{EFG_PREFIX}BackwardInduction",
    f"{EFG_PREFIX}ZeroSumGameTreeWithChance",
}

FORBIDDEN_ROOT_MODULES = {
    f"{EFG_PREFIX}Execution.InfiniteTrajectory",
    f"{EFG_PREFIX}Observed.InfiniteExecution",
    f"{EFG_PREFIX}Interface.Execution.Infinite",
    f"{EFG_PREFIX}Interface.Execution.Discrete",
    f"{EFG_PREFIX}GameTreeSPE",
    f"{EFG_PREFIX}GameTreeNE",
    f"{EFG_PREFIX}GameTreeStrategicForm",
    f"{EFG_PREFIX}FiniteArenaExtraction",
    f"{EFG_PREFIX}Zermelo",
}

MOVED_PATHS = {
    f"{EFG_PREFIX}Simulation.KernelArena":
        f"{EFG_PREFIX}Execution.Discrete.KernelArena",
    f"{EFG_PREFIX}Simulation.KernelTrajectory":
        f"{EFG_PREFIX}Execution.Discrete.KernelTrajectory",
    f"{EFG_PREFIX}Simulation.Morphism":
        f"{EFG_PREFIX}Relations.Discrete.Morphism",
    f"{EFG_PREFIX}Simulation.KernelWeakSimulation":
        f"{EFG_PREFIX}Relations.Discrete.KernelWeakSimulation",
    f"{EFG_PREFIX}Simulation.DiscreteInfinitePathBridge":
        f"{EFG_PREFIX}Simulation.Kernel.DiscreteBridge",
    f"{EFG_PREFIX}Simulation.MeasurableKernelArena":
        f"{EFG_PREFIX}Simulation.Kernel.Arena",
    f"{EFG_PREFIX}Simulation.MeasurableKernelExecution":
        f"{EFG_PREFIX}Simulation.Kernel.Execution",
    f"{EFG_PREFIX}Simulation.MeasurableKernelEndpoint":
        f"{EFG_PREFIX}Simulation.Kernel.Endpoint",
    f"{EFG_PREFIX}Simulation.MeasurableKernelPath":
        f"{EFG_PREFIX}Simulation.Kernel.StatePath",
    f"{EFG_PREFIX}Simulation.MeasurableKernelHistoryPath":
        f"{EFG_PREFIX}Simulation.Kernel.HistoryPath",
    f"{EFG_PREFIX}Simulation.MeasurableKernelEventPath":
        f"{EFG_PREFIX}Simulation.Kernel.EventPath",
    f"{EFG_PREFIX}Simulation.MeasurableKernelObservedEvent":
        f"{EFG_PREFIX}Simulation.Kernel.ObservedEvent",
    f"{EFG_PREFIX}Simulation.MeasurableKernelRealizedInformation":
        f"{EFG_PREFIX}Simulation.Kernel.RealizedInformation",
    f"{EFG_PREFIX}Simulation.ObservedChanceKernelBridge":
        f"{EFG_PREFIX}Simulation.Presentation.Chance.KernelBridge",
    f"{EFG_PREFIX}Simulation.ObservedChanceRealizedPresentation":
        f"{EFG_PREFIX}Simulation.Presentation.Chance.Realized",
    f"{EFG_PREFIX}Simulation.ObservedChanceCountablePresentation":
        f"{EFG_PREFIX}Simulation.Presentation.Chance.Countable",
    f"{EFG_PREFIX}Simulation.ObservedChanceMeasurableHistory":
        f"{EFG_PREFIX}Simulation.Presentation.Chance.MeasurableHistory",
    f"{EFG_PREFIX}Simulation.ObservedChanceMeasurablePresentation":
        f"{EFG_PREFIX}Simulation.Presentation.Chance.Measurable",
    f"{EFG_PREFIX}Simulation.ObservedChanceMeasurableProfileAssembly":
        f"{EFG_PREFIX}Simulation.Presentation.Chance.ProfileAssembly",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelPresentation":
        f"{EFG_PREFIX}Simulation.Presentation.Kernel.Core",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelProfileAssembly":
        f"{EFG_PREFIX}Simulation.Presentation.Kernel.ProfileAssembly",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelOutcome":
        f"{EFG_PREFIX}Simulation.Equilibrium.Outcome",
    f"{EFG_PREFIX}Simulation.MeasurableKernelContinuationPath":
        f"{EFG_PREFIX}Simulation.Continuation.Path",
    f"{EFG_PREFIX}Simulation.MeasurableKernelContinuationConditioning":
        f"{EFG_PREFIX}Simulation.Continuation.Conditioning",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelContinuation":
        f"{EFG_PREFIX}Simulation.Continuation.Observed",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelContinuationConditioning":
        f"{EFG_PREFIX}Simulation.Continuation.ObservedConditioning",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelRestart.Core":
        f"{EFG_PREFIX}Simulation.Restart.Core",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelRestart.Trajectory":
        f"{EFG_PREFIX}Simulation.Restart.Trajectory",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelRestart.Certificates":
        f"{EFG_PREFIX}Simulation.Restart.Certificates",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelRestart.Observed":
        f"{EFG_PREFIX}Simulation.Restart.Observed",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelRestart.Assembly":
        f"{EFG_PREFIX}Simulation.Restart.Assembly",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelRestart.Equilibrium":
        f"{EFG_PREFIX}Simulation.Restart.Equilibrium",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelRestartFactorization":
        f"{EFG_PREFIX}Simulation.Restart.Factorization",
}

HISTORICAL_IMPORT_ALLOWLIST = {
    (
        f"{EFG_PREFIX}Compiler.GameTreeOccurrenceObserved",
        f"{EFG_PREFIX}Compiler.GameTreeObserved",
    ): (
        "the occurrence-sensitive compiler proves exact refinement and "
        "strategy-lifting bridges to the retained endpoint compiler"
    ),
    (
        f"{EFG_PREFIX}FiniteArenaExtraction",
        f"{EFG_PREFIX}GameTreeNE",
    ): (
        "the extraction frontend preserves the historical endpoint-policy "
        "subgame-perfect-to-root-Nash theorem"
    ),
    (
        f"{EFG_PREFIX}Zermelo",
        f"{EFG_PREFIX}GameTreeNE",
    ): (
        "the specialized Zermelo frontend states retained endpoint-policy "
        "Kuhn and Nash corollaries"
    ),
}

FORBIDDEN_DIRECT_IMPORTS = {
    (
        f"{EFG_PREFIX}Execution.History",
        f"{EFG_PREFIX}Subgame",
    ): "canonical history infrastructure must depend only on reachability",
    (
        f"{EFG_PREFIX}StochasticGameTree",
        f"{EFG_PREFIX}GameTreeSPE",
    ): "stochastic tree syntax needs only the structural GameTree module",
}

# These modules form the payoff-free dependency spine.  Their complete local
# import closures must not reach legacy payoff-aware observed games,
# compatibility adapters, equilibrium/simulation implementations, or the
# payoff-aware winning layer.
PAYOFF_FREE_CORE_BOUNDARIES = {
    f"{EFG_PREFIX}Execution.DependentFiber",
    f"{EFG_PREFIX}Execution.StochasticNaturality",
    f"{EFG_PREFIX}Observed.Controlled",
    f"{EFG_PREFIX}Observed.ControlledInfrastructure",
    f"{EFG_PREFIX}Observed.ControlledInfrastructure.Core",
    CONTROLLED_INFRASTRUCTURE_WELL_FORMED,
    f"{EFG_PREFIX}Observed.ControlledInfrastructure.Subgame",
    f"{EFG_PREFIX}Observed.ControlledInfrastructure.Finite",
    f"{EFG_PREFIX}Observed.ControlledInfrastructure.Quasi",
    f"{EFG_PREFIX}Observed.ControlledInfrastructure.Recall",
    f"{EFG_PREFIX}Observed.ControlledMorphism",
    CONTROLLED_MORPHISM_CORE,
    CONTROLLED_MORPHISM_SUBGAME,
    CONTROLLED_MORPHISM_RECALL,
    f"{EFG_PREFIX}Observed.ControlledSemantics",
    f"{EFG_PREFIX}Observed.ControlledDiscreteLaw",
    f"{EFG_PREFIX}Observed.ControlledLaw",
    f"{EFG_PREFIX}Winning.Basic",
    f"{EFG_PREFIX}Winning.Determinacy",
    STRUCTURAL_CORE,
    f"{EFG_PREFIX}Interface.Core",
}

FORBIDDEN_PAYOFF_FREE_CLOSURE_MODULES = {
    f"{EFG_PREFIX}Observed.Game",
    f"{EFG_PREFIX}Observed.Semantics",
    f"{EFG_PREFIX}Observed.WellFormed",
    f"{EFG_PREFIX}Observed.Quasi",
    f"{EFG_PREFIX}Observed.PerfectRecall",
    f"{EFG_PREFIX}Observed.SignalRecall",
    f"{EFG_PREFIX}Observed.Chance",
    f"{EFG_PREFIX}Observed.Behavior",
    f"{EFG_PREFIX}Observed.InfiniteExecution",
    f"{EFG_PREFIX}Observed.ControlledInfrastructureCompat",
    f"{EFG_PREFIX}Observed.ControlledMorphismCompat",
    f"{EFG_PREFIX}Observed.ControlledDiscreteLawCompat",
    f"{EFG_PREFIX}Winning.BasicCompat",
    f"{EFG_PREFIX}Winning.DeterminacyCompat",
}

FORBIDDEN_PAYOFF_FREE_CLOSURE_PREFIXES = (
    f"{EFG_PREFIX}Observed.Morphism.",
    f"{EFG_PREFIX}Observed.Equilibrium",
    f"{EFG_PREFIX}Simulation.",
    f"{EFG_PREFIX}Interface.Equilibrium",
)

MAXIMUM_PATH_LAW_MODULE = f"{EFG_PREFIX}Observed.ControlledLaw"
MAXIMUM_PATH_LAW_FORBIDDEN_NAMES = {
    "PMF",
    "Countable",
    "DiscreteControlledObservedChanceGame",
    "ObservedGame",
}

FORBIDDEN_LEGACY_ROOT_NAMES = {
    "IsDesignatedContinuationRoot",
    "legacyContinuationRootPresentation",
}


@dataclass(frozen=True)
class StatusRow:
    module: str
    status: str
    responsibility: str
    recommended_import: str
    replacement: str
    may_grow: str
    action: str
    removal_policy: str


def module_name(path: Path, root: Path) -> str | None:
    relative = path.relative_to(root)
    if relative == Path("EconCSLib.lean"):
        return "EconCSLib"
    if not relative.parts or relative.parts[0] != "EconCSLib":
        return None
    return ".".join(relative.with_suffix("").parts)


def module_path(module: str, root: Path) -> Path:
    if module == "EconCSLib":
        return root / "EconCSLib.lean"
    return root / Path(*module.split(".")).with_suffix(".lean")


def in_scope_modules(root: Path) -> set[str]:
    paths = list((root / "EconCSLib/GameTheory/ExtensiveGame").rglob("*.lean"))
    paths += [root / "EconCSLib/GameTheory/GameForm.lean"]
    paths += list((root / "EconCSLib/GameTheory/GameForm").rglob("*.lean"))
    paths += [root / "EconCSLib/Math/Probability/PMF.lean"]
    paths += list((root / "EconCSLib/Math/Probability/PMF").rglob("*.lean"))
    return {
        name
        for path in paths
        if path.is_file() and (name := module_name(path, root)) is not None
    }


def read_status_rows(path: Path) -> tuple[dict[str, StatusRow], list[str]]:
    rows: dict[str, StatusRow] = {}
    errors: list[str] = []
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not MODULE_ROW_RE.match(line):
            continue
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if len(cells) != 8:
            errors.append(
                f"{path}:{line_no}: expected 8 module-table cells, found {len(cells)}"
            )
            continue
        module = cells[0].strip("`")
        if module in rows:
            errors.append(f"{path}:{line_no}: duplicate module row for {module}")
            continue
        rows[module] = StatusRow(module, *cells[1:])
    return rows, errors


def strip_lean_comments_and_strings(text: str) -> str:
    """Replace nested comments, line comments, strings, and chars with spaces."""

    output: list[str] = []
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    in_char = False
    while index < len(text):
        char = text[index]
        next_char = text[index + 1] if index + 1 < len(text) else ""
        if in_line_comment:
            if char == "\n":
                in_line_comment = False
                output.append(char)
            else:
                output.append(" ")
            index += 1
        elif block_depth:
            if char == "/" and next_char == "-":
                block_depth += 1
                output.extend("  ")
                index += 2
            elif char == "-" and next_char == "/":
                block_depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
        elif in_string or in_char:
            delimiter = '"' if in_string else "'"
            if char == "\\" and next_char:
                output.extend("  ")
                index += 2
            elif char == delimiter:
                in_string = False
                in_char = False
                output.append(" ")
                index += 1
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
        elif char == "-" and next_char == "-":
            in_line_comment = True
            output.extend("  ")
            index += 2
        elif char == "/" and next_char == "-":
            block_depth = 1
            output.extend("  ")
            index += 2
        elif char == '"':
            in_string = True
            output.append(" ")
            index += 1
        elif char == "'":
            in_char = True
            output.append(" ")
            index += 1
        else:
            output.append(char)
            index += 1
    return "".join(output)


def local_import_graph(root: Path) -> tuple[dict[str, set[str]], list[str]]:
    graph: dict[str, set[str]] = {}
    errors: list[str] = []
    for path in root.rglob("*.lean"):
        if ".lake" in path.parts:
            continue
        module = module_name(path, root)
        if module is None:
            continue
        imports = set(IMPORT_RE.findall(path.read_text(encoding="utf-8")))
        graph[module] = imports
    for importer, imports in graph.items():
        for imported in imports:
            if imported.startswith("EconCSLib") and imported not in graph:
                errors.append(
                    f"{module_path(importer, root)}: unresolved local import {imported}"
                )
    return graph, errors


def closure(graph: dict[str, set[str]], entry: str) -> set[str]:
    visited: set[str] = set()
    pending = list(graph[entry])
    while pending:
        module = pending.pop()
        if module in visited or module not in graph:
            continue
        visited.add(module)
        pending.extend(graph[module])
    return visited


def import_cycle(
    graph: dict[str, set[str]], modules: set[str]
) -> list[str] | None:
    """Return one in-scope import cycle, including the repeated endpoint."""

    state: dict[str, int] = {}
    path: list[str] = []

    def visit(module: str) -> list[str] | None:
        state[module] = 1
        path.append(module)
        for imported in sorted(graph.get(module, set())):
            if imported not in modules:
                continue
            if state.get(imported, 0) == 1:
                start = path.index(imported)
                return path[start:] + [imported]
            if state.get(imported, 0) == 0:
                found = visit(imported)
                if found is not None:
                    return found
        path.pop()
        state[module] = 2
        return None

    for module in sorted(modules):
        if state.get(module, 0) == 0:
            found = visit(module)
            if found is not None:
                return found
    return None


def compatibility_import_allowed(importer: str, rows: dict[str, StatusRow]) -> bool:
    if (
        rows.get(importer, StatusRow("", "", "", "", "", "", "", "")).status
        == "Compatibility"
    ):
        return True
    return (
        importer.startswith("EconCSLib.Examples.ExtensiveGame.")
        and importer.endswith("ImportBoundary")
    )


def run(root: Path) -> list[str]:
    errors: list[str] = []
    status_path = root / "docs/design/efg-module-status.md"
    migration_path = root / "docs/design/efg-api-migration.md"
    rows, row_errors = read_status_rows(status_path)
    errors.extend(row_errors)

    scoped = in_scope_modules(root)
    registered = set(rows)
    for module in sorted(scoped - registered):
        errors.append(f"{status_path}: missing module row for {module}")
    for module in sorted(registered - scoped):
        errors.append(f"{status_path}: row has no in-scope source module: {module}")

    graph, graph_errors = local_import_graph(root)
    errors.extend(graph_errors)
    cycle = import_cycle(graph, scoped)
    if cycle is not None:
        errors.append("local import graph contains a cycle: " + " -> ".join(cycle))

    for pair, reason in HISTORICAL_IMPORT_ALLOWLIST.items():
        importer, imported = pair
        if not reason.strip():
            errors.append(
                "historical import allowlist entry must include a reason: "
                f"{importer} -> {imported}"
            )
        if imported not in graph.get(importer, set()):
            errors.append(
                "stale historical import allowlist entry: "
                f"{importer} -> {imported}"
            )
        if rows.get(imported) is None or rows[imported].status != "Historical":
            errors.append(
                "historical import allowlist target is not registered Historical: "
                f"{imported}"
            )

    protected_importers = {"Canonical", "Frontend", "Internal"}
    for importer, imports in graph.items():
        importer_row = rows.get(importer)
        if importer_row is None or importer_row.status not in protected_importers:
            continue
        for imported in sorted(imports):
            imported_row = rows.get(imported)
            if (
                imported_row is not None
                and imported_row.status == "Historical"
                and (importer, imported) not in HISTORICAL_IMPORT_ALLOWLIST
            ):
                errors.append(
                    f"{module_path(importer, root)}: {importer_row.status} module "
                    f"imports Historical module {imported} without an exact "
                    "allowlist entry"
                )

    for (importer, imported), reason in FORBIDDEN_DIRECT_IMPORTS.items():
        if imported in graph.get(importer, set()):
            errors.append(
                f"{module_path(importer, root)}: forbidden direct import "
                f"{imported} ({reason})"
            )

    for entry in sorted(PAYOFF_FREE_CORE_BOUNDARIES):
        if entry not in graph:
            errors.append(f"missing payoff-free boundary module: {entry}")
            continue
        imported = closure(graph, entry)
        for module in sorted(imported):
            if (
                module in FORBIDDEN_PAYOFF_FREE_CLOSURE_MODULES
                or module.startswith(FORBIDDEN_PAYOFF_FREE_CLOSURE_PREFIXES)
            ):
                errors.append(
                    f"{module_path(entry, root)}: payoff-free closure reaches "
                    f"forbidden downstream module {module}"
                )

    maximum_law_path = module_path(MAXIMUM_PATH_LAW_MODULE, root)
    maximum_law_source = strip_lean_comments_and_strings(
        maximum_law_path.read_text(encoding="utf-8")
    )
    for name in sorted(MAXIMUM_PATH_LAW_FORBIDDEN_NAMES):
        if re.search(rf"\b{re.escape(name)}\b", maximum_law_source):
            errors.append(
                f"{maximum_law_path}: maximum path-law interface contains "
                f"forbidden discrete/payoff-aware name {name}"
            )
    for required in ("pathLaw_isProbability", "pathLaw_ae_legal"):
        if not re.search(rf"\b{required}\b", maximum_law_source):
            errors.append(
                f"{maximum_law_path}: lawful probability carrier is missing "
                f"required field {required}"
            )

    for module in sorted(scoped):
        path = module_path(module, root)
        stripped = strip_lean_comments_and_strings(
            path.read_text(encoding="utf-8")
        )
        for name in sorted(FORBIDDEN_LEGACY_ROOT_NAMES):
            if re.search(rf"\b{re.escape(name)}\b", stripped):
                errors.append(
                    f"{path}: forbidden legacy continuation-root API {name}; "
                    "pass RootPresentation or a lawful subgame system explicitly"
                )

    compatibility = {
        module for module, row in rows.items() if row.status == "Compatibility"
    }
    for module in sorted(compatibility):
        path = module_path(module, root)
        source = path.read_text(encoding="utf-8")
        stripped = strip_lean_comments_and_strings(source)
        if DECLARATION_RE.search(stripped):
            errors.append(f"{path}: compatibility module defines a declaration")
        residue = IMPORT_RE.sub("", stripped)
        if residue.strip():
            errors.append(f"{path}: compatibility module must contain only imports")
        row = rows[module]
        if row.action != "Thin wrapper":
            errors.append(f"{status_path}: {module} action must be Thin wrapper")
        if not row.replacement or row.replacement == "—":
            errors.append(f"{status_path}: {module} must name a replacement")

    for importer, imports in graph.items():
        imported_compatibility = imports & compatibility
        if imported_compatibility and not compatibility_import_allowed(importer, rows):
            joined = ", ".join(sorted(imported_compatibility))
            errors.append(
                f"{module_path(importer, root)}: implementation imports "
                f"compatibility aggregate(s): {joined}"
            )

    for entry, expected in EXPECTED_CLOSURES.items():
        if entry not in graph:
            errors.append(f"missing facade or aggregate module: {entry}")
            continue
        imported = closure(graph, entry)
        actual = (
            sum(module.startswith(EFG_PREFIX) for module in imported),
            len(imported),
        )
        if actual != expected:
            errors.append(
                f"{module_path(entry, root)}: closure is {actual[0]} EFG / "
                f"{actual[1]} local; expected {expected[0]} / {expected[1]}"
            )

    for entry, expected in EXPECTED_EXACT_EFG_CLOSURES.items():
        if entry not in graph:
            errors.append(f"missing exact-closure boundary module: {entry}")
            continue
        actual = {
            module
            for module in closure(graph, entry)
            if module.startswith(EFG_PREFIX)
        }
        if actual != expected:
            missing = sorted(expected - actual)
            extra = sorted(actual - expected)
            errors.append(
                f"{module_path(entry, root)}: exact EFG closure differs; "
                f"missing={missing}, extra={extra}"
            )

    for aggregate, expected_imports in EXPECTED_COMPATIBILITY_AGGREGATE_IMPORTS.items():
        actual_imports = graph.get(aggregate)
        if actual_imports is None:
            errors.append(f"missing controlled compatibility aggregate: {aggregate}")
        elif actual_imports != expected_imports:
            errors.append(
                f"{module_path(aggregate, root)}: direct imports differ from "
                f"the compatibility contract; expected={sorted(expected_imports)}, "
                f"actual={sorted(actual_imports)}"
            )

    structural_core_closure = closure(graph, STRUCTURAL_CORE)
    structural_core_efg_closure = {
        module
        for module in structural_core_closure
        if module.startswith(EFG_PREFIX)
    }
    if structural_core_efg_closure != EXPECTED_STRUCTURAL_CORE_EFG_CLOSURE:
        missing = sorted(
            EXPECTED_STRUCTURAL_CORE_EFG_CLOSURE - structural_core_efg_closure
        )
        extra = sorted(
            structural_core_efg_closure - EXPECTED_STRUCTURAL_CORE_EFG_CLOSURE
        )
        errors.append(
            f"{module_path(STRUCTURAL_CORE, root)}: structural EFG closure "
            f"differs from the exact five-module boundary; missing={missing}, "
            f"extra={extra}"
        )

    core_module = f"{EFG_PREFIX}Interface.Core"
    core_closure = closure(graph, core_module)
    for module in sorted(core_closure):
        if (
            module in CORE_FORBIDDEN_CLOSURE_MODULES
            or module.startswith(CORE_FORBIDDEN_CLOSURE_PREFIXES)
        ):
            errors.append(
                f"{module_path(core_module, root)}: Foundation Facade closure "
                f"reaches forbidden objective/winning module {module}"
            )

    root_imports = graph.get("EconCSLib", set())
    actual_root_efg_imports = {
        module for module in root_imports if module.startswith(EFG_PREFIX)
    }
    if actual_root_efg_imports != EXPECTED_ROOT_EFG_IMPORTS:
        errors.append(
            "EconCSLib.lean: direct EFG imports differ from the governed "
            f"finite root: {sorted(actual_root_efg_imports)}"
        )

    root_closure = closure(graph, "EconCSLib")
    for module in sorted(root_closure):
        row = rows.get(module)
        if row is not None and row.status in {"Historical", "Compatibility"}:
            errors.append(
                f"EconCSLib.lean: root closure contains {row.status} module {module}"
            )
    for module in sorted(root_closure & FORBIDDEN_ROOT_MODULES):
        errors.append(f"EconCSLib.lean: forbidden root dependency {module}")
    for module in sorted(root_closure):
        if module.startswith(
            (
                f"{EFG_PREFIX}Compiler.",
                f"{EFG_PREFIX}FOSG.",
                f"{EFG_PREFIX}Simulation.",
            )
        ):
            errors.append(f"EconCSLib.lean: forbidden root dependency {module}")

    restart = closure(graph, f"{EFG_PREFIX}Interface.Restart")
    compilation = closure(graph, f"{EFG_PREFIX}Interface.Compilation.Discrete")
    if any(module.startswith(f"{EFG_PREFIX}Interface.Compilation") for module in restart):
        errors.append("Interface.Restart must not depend on Compilation")
    if any(module == f"{EFG_PREFIX}Interface.Restart" for module in compilation):
        errors.append("Interface.Compilation.Discrete must not depend on Restart")

    pmf_modules = {
        module
        for module in graph
        if module == "EconCSLib.Math.Probability.PMF"
        or module.startswith("EconCSLib.Math.Probability.PMF.")
    }
    for module in sorted(pmf_modules):
        for imported in sorted(graph[module]):
            if imported.startswith("EconCSLib.GameTheory."):
                errors.append(
                    f"{module_path(module, root)}: reusable PMF layer imports {imported}"
                )

    for importer, imports in graph.items():
        if (
            importer in {"EconCSLib.Examples", "EconCSLib.OpenProblem"}
            or importer.startswith(
                ("EconCSLib.Examples.", "EconCSLib.OpenProblem.")
            )
        ):
            continue
        for imported in imports:
            if imported.startswith(
                ("EconCSLib.Examples.", "EconCSLib.OpenProblem.")
            ):
                errors.append(
                    f"{module_path(importer, root)}: stable source imports {imported}"
                )

    for old, new in MOVED_PATHS.items():
        if old in graph or module_path(old, root).exists():
            errors.append(f"obsolete internal module path still exists: {old}")
        if new not in graph:
            errors.append(f"moved internal module is missing: {new}")

    migration = migration_path.read_text(encoding="utf-8")
    for module in sorted(scoped):
        source = module_path(module, root).read_text(encoding="utf-8")
        for name in DEPRECATED_RE.findall(source):
            if name not in migration:
                errors.append(
                    f"{module_path(module, root)}: deprecated declaration "
                    f"{name} is absent from {migration_path}"
                )

    simulation_count = sum(
        module.startswith(f"{EFG_PREFIX}Simulation.") for module in scoped
    )
    if simulation_count != 30:
        errors.append(
            f"Simulation module count is {simulation_count}; expected governed count 30"
        )

    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="repository root (defaults to the script's parent repository)",
    )
    args = parser.parse_args()
    root = args.root.resolve()
    errors = run(root)
    if errors:
        for error in errors:
            print(f"EFG governance error: {error}", file=sys.stderr)
        return 1

    rows, _ = read_status_rows(root / "docs/design/efg-module-status.md")
    graph, _ = local_import_graph(root)
    root_imported = closure(graph, "EconCSLib")
    root_counts = (
        sum(module.startswith(EFG_PREFIX) for module in root_imported),
        len(root_imported),
    )
    compatibility_count = sum(
        row.status == "Compatibility" for row in rows.values()
    )
    simulation_count = sum(
        module.startswith(f"{EFG_PREFIX}Simulation.") for module in rows
    )
    print(
        f"EFG governance checks passed: {len(rows)} registered modules, "
        f"{compatibility_count} import-only compatibility paths, "
        f"root {root_counts[0]}/{root_counts[1]}, "
        f"Simulation {simulation_count}."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
