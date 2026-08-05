#!/usr/bin/env python3
"""Enforce the repository's mechanically checkable per-commit scope rules."""

from __future__ import annotations

import argparse
import subprocess
import sys
from dataclasses import dataclass


def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], text=True).strip()


def is_merge_commit(commit: str) -> bool:
    return len(git("rev-list", "--parents", "-n", "1", commit).split()) > 2


@dataclass(frozen=True)
class ChangedFile:
    """One logical file operation, including a detected rename."""

    status: str
    paths: tuple[str, ...]

    @property
    def current_path(self) -> str:
        return self.paths[-1]


def changed_files(commit: str) -> list[ChangedFile]:
    entries: list[ChangedFile] = []
    output = git(
        "diff-tree",
        "--root",
        "--no-commit-id",
        "--name-status",
        "--find-renames",
        "-r",
        commit,
    )
    for line in output.splitlines():
        fields = line.split("\t")
        if len(fields) < 2:
            continue
        entries.append(ChangedFile(fields[0], tuple(fields[1:])))
    return entries


def added_structure_or_class_count(commit: str, paths: tuple[str, ...]) -> int:
    diff = git(
        "diff",
        "--find-renames",
        "--unified=0",
        f"{commit}^!",
        "--",
        *paths,
    )
    count = 0
    for line in diff.splitlines():
        if not line.startswith("+") or line.startswith("+++"):
            continue
        code = line[1:].lstrip()
        if code.startswith("--"):
            continue
        if code.startswith("structure ") or code.startswith("class "):
            count += 1
    return count


def partition_grandfathered_commits(
    commits: list[str],
    grandfathered_ancestry: set[str],
) -> tuple[list[str], list[str]]:
    grandfathered = [
        commit for commit in commits if commit in grandfathered_ancestry
    ]
    enforced = [
        commit for commit in commits if commit not in grandfathered_ancestry
    ]
    return enforced, grandfathered


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", required=True)
    parser.add_argument("--head", required=True)
    parser.add_argument(
        "--grandfather-commit",
        action="append",
        default=[],
        help="skip one exact, explicitly audited historical commit",
    )
    args = parser.parse_args()

    commits = git("rev-list", "--reverse", f"{args.base}..{args.head}").splitlines()
    commits, grandfathered = partition_grandfathered_commits(
        commits,
        set(args.grandfather_commit),
    )

    errors: list[str] = []
    for commit in commits:
        if is_merge_commit(commit):
            continue
        files = changed_files(commit)
        if len(files) != 1:
            errors.append(
                f"{commit[:12]} changes {len(files)} logical files; each "
                "non-merge commit must change exactly one logical file"
            )
            continue
        changed = files[0]
        path = changed.current_path
        if path.endswith(".lean"):
            declarations = added_structure_or_class_count(commit, changed.paths)
            if declarations > 1:
                errors.append(
                    f"{commit[:12]} adds {declarations} structures/classes in {path}; at most one is allowed"
                )

    if errors:
        print("\n".join(errors))
        return 1
    if grandfathered:
        print(
            "Commit scope: grandfathered "
            f"{len(grandfathered)} explicitly audited historical commit(s); "
            "checked "
            f"{len(commits)} later commit(s)."
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
