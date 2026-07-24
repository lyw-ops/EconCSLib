#!/usr/bin/env python3
"""Enforce the repository's mechanically checkable per-commit scope rules."""

from __future__ import annotations

import argparse
import subprocess
import sys


def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], text=True).strip()


def is_merge_commit(commit: str) -> bool:
    return len(git("rev-list", "--parents", "-n", "1", commit).split()) > 2


def changed_paths(commit: str) -> list[str]:
    return [
        path
        for path in git("diff-tree", "--root", "--no-commit-id", "--name-only", "-r", commit).splitlines()
        if path
    ]


def added_structure_or_class_count(commit: str, path: str) -> int:
    diff = git("diff", "--unified=0", f"{commit}^!", "--", path)
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


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", required=True)
    parser.add_argument("--head", required=True)
    args = parser.parse_args()

    commits = git("rev-list", "--reverse", f"{args.base}..{args.head}").splitlines()
    errors: list[str] = []
    for commit in commits:
        if is_merge_commit(commit):
            continue
        paths = changed_paths(commit)
        if len(paths) != 1:
            errors.append(
                f"{commit[:12]} changes {len(paths)} files; each non-merge commit must change exactly one file"
            )
            continue
        path = paths[0]
        if path.endswith(".lean"):
            declarations = added_structure_or_class_count(commit, path)
            if declarations > 1:
                errors.append(
                    f"{commit[:12]} adds {declarations} structures/classes in {path}; at most one is allowed"
                )

    if errors:
        print("\n".join(errors))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
