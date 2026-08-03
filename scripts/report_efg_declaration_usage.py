#!/usr/bin/env python3
"""Report heuristic consumers of registered EFG theorem declarations.

This is an API-triage report, not a dead-code oracle.  Lean declarations can
be legitimate public endpoints even when no declaration in this repository
uses them.  The report therefore keeps zero-indegree, documentation, example,
test, privacy, and lifecycle evidence separate.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
REGISTER = ROOT / "docs/design/efg-module-status.md"
LIFECYCLES = (
    "Canonical",
    "Frontend",
    "Historical",
    "Compatibility",
    "Experimental",
    "Internal",
)
MODULE_ROW_RE = re.compile(
    r"^\| `(?P<module>EconCSLib[^`]+)` \| "
    r"(?P<lifecycle>"
    + "|".join(LIFECYCLES)
    + r") \|",
    re.MULTILINE,
)
DECL_RE = re.compile(
    r"^[ \t]*(?P<prefix>(?:(?:private|protected|noncomputable)[ \t]+)*)"
    r"(?P<kind>theorem|lemma)[ \t\r\n]+"
    r"(?P<name>[^\s(:\[\{]+)",
    re.MULTILINE,
)
TOKEN_RE = re.compile(r"[^\W\d][\w']*", re.UNICODE)
PRIVATE_ROUTE_MARKERS = (
    "_viaContinuationFamily",
    "_viaInformationRefinement",
    "_viaContinuationSimulation",
)
PUBLIC_ENDPOINT_LIFECYCLES = ("Canonical", "Frontend")
# Current triage ceiling. The baseline does not claim that every item has
# already received mathematical review. New zero-source-indegree public
# endpoints must either have documentation/example/test evidence or avoid
# growing the manual review queue.
MAX_PUBLIC_ENDPOINT_REVIEW = 263


@dataclass(frozen=True)
class Declaration:
    module: str
    lifecycle: str
    path: Path
    kind: str
    name: str
    line: int
    is_private: bool


@dataclass(frozen=True)
class Usage:
    declaration: Declaration
    source_references: int
    example_references: int
    documentation_references: int
    test_references: int

    @property
    def zero_indegree(self) -> bool:
        return self.source_references == 0

    @property
    def has_endpoint_evidence(self) -> bool:
        return (
            self.documentation_references
            + self.example_references
            + self.test_references
        ) > 0

    @property
    def triage_queue(self) -> str:
        """Conservative review queue; never an automatic deletion decision."""

        if not self.zero_indegree:
            return "source-used"
        if self.has_endpoint_evidence:
            return "evidenced-endpoint"
        if self.declaration.is_private:
            return "private-review"
        if self.declaration.lifecycle == "Internal":
            return "internal-review"
        if self.declaration.lifecycle == "Historical":
            return "historical-review"
        if self.declaration.lifecycle in PUBLIC_ENDPOINT_LIFECYCLES:
            return "public-endpoint-review"
        return "lifecycle-review"


def module_path(module: str) -> Path:
    parts = module.split(".")
    if parts[0] != "EconCSLib":
        raise ValueError(f"unsupported module outside EconCSLib: {module}")
    return ROOT.joinpath(*parts).with_suffix(".lean")


def read_module_register() -> list[tuple[str, str, Path]]:
    text = REGISTER.read_text(encoding="utf-8")
    rows: list[tuple[str, str, Path]] = []
    seen: set[str] = set()
    for match in MODULE_ROW_RE.finditer(text):
        module = match.group("module")
        lifecycle = match.group("lifecycle")
        if module in seen:
            raise ValueError(f"duplicate lifecycle row: {module}")
        seen.add(module)
        path = module_path(module)
        if not path.is_file():
            raise FileNotFoundError(
                f"registered module has no source file: {module} ({path})"
            )
        rows.append((module, lifecycle, path))
    if not rows:
        raise ValueError(f"no module rows found in {REGISTER}")
    return rows


def declarations(
    rows: list[tuple[str, str, Path]],
) -> tuple[list[Declaration], Counter[str]]:
    found: list[Declaration] = []
    declaration_names: Counter[str] = Counter()
    for module, lifecycle, path in rows:
        text = path.read_text(encoding="utf-8")
        for match in DECL_RE.finditer(text):
            name = match.group("name")
            prefix = match.group("prefix").split()
            found.append(
                Declaration(
                    module=module,
                    lifecycle=lifecycle,
                    path=path,
                    kind=match.group("kind"),
                    name=name,
                    line=text.count("\n", 0, match.start()) + 1,
                    is_private="private" in prefix,
                )
            )
            declaration_names[name.rsplit(".", 1)[-1]] += 1
    return found, declaration_names


def token_counts(paths: list[Path]) -> Counter[str]:
    counts: Counter[str] = Counter()
    for path in paths:
        if path.is_file():
            counts.update(TOKEN_RE.findall(path.read_text(encoding="utf-8")))
    return counts


def repository_usage(
    rows: list[tuple[str, str, Path]],
    found: list[Declaration],
    declaration_names: Counter[str],
) -> list[Usage]:
    registered_paths = [path for _module, _lifecycle, path in rows]
    source_counts = token_counts(registered_paths)
    example_counts = token_counts(
        sorted((ROOT / "EconCSLib/Examples").rglob("*.lean"))
    )
    documentation_counts = token_counts(sorted((ROOT / "docs").rglob("*.md")))
    test_counts = token_counts(
        sorted((ROOT / "tests").rglob("*.py"))
        + sorted((ROOT / "scripts").rglob("*.py"))
    )

    usage: list[Usage] = []
    for declaration in found:
        name = declaration.name.rsplit(".", 1)[-1]
        usage.append(
            Usage(
                declaration=declaration,
                source_references=max(
                    0, source_counts[name] - declaration_names[name]
                ),
                example_references=example_counts[name],
                documentation_references=documentation_counts[name],
                test_references=test_counts[name],
            )
        )
    return usage


def public_route_regressions(usage: list[Usage]) -> list[Declaration]:
    return [
        item.declaration
        for item in usage
        if not item.declaration.is_private
        and item.declaration.lifecycle != "Internal"
        and any(marker in item.declaration.name for marker in PRIVATE_ROUTE_MARKERS)
    ]


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def render_report(usage: list[Usage]) -> str:
    by_lifecycle: dict[str, list[Usage]] = defaultdict(list)
    for item in usage:
        by_lifecycle[item.declaration.lifecycle].append(item)

    lines = [
        "# EFG Declaration Usage Report",
        "",
        "Generated by `scripts/report_efg_declaration_usage.py` from the",
        "lifecycle register and the current source tree.",
        "",
        "> This is a conservative textual dependency report, not a deletion",
        "> list. A zero-indegree theorem may be an intentional public endpoint.",
        "> Short-name collisions can only hide candidates; they do not create",
        "> false zero-indegree findings.",
        "",
        "## Summary",
        "",
        "| Lifecycle | Theorems/lemmas | Zero source indegree | Evidenced endpoints | Public endpoint review | Internal/private review |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for lifecycle in LIFECYCLES:
        items = by_lifecycle.get(lifecycle, [])
        lines.append(
            f"| {lifecycle} | {len(items)} | "
            f"{sum(item.zero_indegree for item in items)} | "
            f"{sum(item.triage_queue == 'evidenced-endpoint' for item in items)} | "
            f"{sum(item.triage_queue == 'public-endpoint-review' for item in items)} | "
            f"{sum(item.triage_queue in ('internal-review', 'private-review') for item in items)} |"
        )

    zero_items = sorted(
        (item for item in usage if item.zero_indegree),
        key=lambda item: (
            LIFECYCLES.index(item.declaration.lifecycle),
            item.declaration.module,
            item.declaration.line,
        ),
    )
    lines.extend(
        [
            "",
            "## Zero-source-indegree declarations",
            "",
            "| Queue | Lifecycle | Visibility | Declaration | Owner | Docs | Examples | Tests |",
            "|---|---|---|---|---|---:|---:|---:|",
        ]
    )
    for item in zero_items:
        declaration = item.declaration
        visibility = "private" if declaration.is_private else "name-resolvable"
        owner = f"`{rel(declaration.path)}:{declaration.line}`"
        lines.append(
            f"| {item.triage_queue} | {declaration.lifecycle} | {visibility} | "
            f"`{declaration.name}` | {owner} | "
            f"{item.documentation_references} | {item.example_references} | "
            f"{item.test_references} |"
        )

    lines.extend(
        [
            "",
            "## Triage rule",
            "",
            "A declaration is a deletion or privatization candidate only after",
            "confirming that it has no source consumer, documentation role,",
            "example/test role, or intended public-endpoint role. Lifecycle",
            "policy remains authoritative. `public-endpoint-review` means the",
            "declaration needs an explicit endpoint role or a downstream",
            "consumer; it does not mean the declaration is dead code.",
            "",
        ]
    )
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output",
        type=Path,
        help="write the Markdown report to this path; stdout gets a summary",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail when a route-regression theorem leaks from private/Internal scope",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        rows = read_module_register()
        found, declaration_names = declarations(rows)
        usage = repository_usage(rows, found, declaration_names)
    except (OSError, ValueError) as error:
        print(f"EFG declaration report error: {error}", file=sys.stderr)
        return 2

    report = render_report(usage)
    zero_count = sum(item.zero_indegree for item in usage)
    public_review_count = sum(
        item.triage_queue == "public-endpoint-review" for item in usage
    )
    route_leaks = public_route_regressions(usage)

    if args.output:
        output = args.output
        if not output.is_absolute():
            output = ROOT / output
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(report, encoding="utf-8")
        print(f"Wrote {output}")
    else:
        print(report)

    print(
        f"EFG declaration usage: {len(rows)} modules, {len(usage)} "
        f"theorems/lemmas, {zero_count} zero-source-indegree candidates, "
        f"{public_review_count} public-endpoint-review"
    )
    if route_leaks:
        print(
            "Public route-regression declarations must be private or Internal:",
            file=sys.stderr,
        )
        for declaration in route_leaks:
            print(
                f"  {rel(declaration.path)}:{declaration.line}: "
                f"{declaration.name}",
                file=sys.stderr,
            )
    public_review_growth = (
        public_review_count > MAX_PUBLIC_ENDPOINT_REVIEW
    )
    if public_review_growth:
        print(
            "Unexplained public endpoint review queue grew beyond the "
            f"{MAX_PUBLIC_ENDPOINT_REVIEW} baseline: {public_review_count}",
            file=sys.stderr,
        )
    if args.check and (route_leaks or public_review_growth):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
