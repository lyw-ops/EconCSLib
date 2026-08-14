#!/usr/bin/env python3
"""Defense-in-depth scan for forbidden placeholders/declarations.

This scanner is deliberately conservative and is NOT sufficient on its own.
The harness must also compile the file, inspect warnings, and compare declaration axioms.
"""
from __future__ import annotations
import argparse, re, sys
from pathlib import Path

TOKEN_PATTERNS = {
    "sorry": re.compile(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])"),
    "admit": re.compile(r"(?<![A-Za-z0-9_])admit(?![A-Za-z0-9_])"),
    "native_decide": re.compile(r"(?<![A-Za-z0-9_])native_decide(?![A-Za-z0-9_])"),
}
DECL_PATTERN = re.compile(r"(?m)^\s*(axiom|constant)\s+([A-Za-z_][A-Za-z0-9_'.]*)")
NATIVE_DECIDE_PATTERN = re.compile(r"(?m)\b(?:exact\s+)?decide\b[^\n]*\bnative\b")
DISABLED_LINTER_PATTERN = re.compile(
    r"(?m)\bset_option\s+(?:linter\.[A-Za-z0-9_.]+|warningAsError)\s+false\b"
)

def strip_comments_and_strings(src: str) -> str:
    # Lightweight scanner; Lean parsing remains authoritative.
    out=[]; i=0; depth=0; in_str=False
    while i < len(src):
        if in_str:
            if src[i]=='\\' and i+1<len(src): out.extend('  '); i+=2; continue
            if src[i]=='"': in_str=False
            out.append(' ' if src[i] != '\n' else '\n'); i+=1; continue
        if depth:
            if src.startswith('/-',i): depth+=1; out.extend('  '); i+=2; continue
            if src.startswith('-/',i): depth-=1; out.extend('  '); i+=2; continue
            out.append(' ' if src[i] != '\n' else '\n'); i+=1; continue
        if src.startswith('--',i):
            j=src.find('\n',i); j=len(src) if j<0 else j
            out.extend(' '*(j-i)); i=j; continue
        if src.startswith('/-',i): depth=1; out.extend('  '); i+=2; continue
        if src[i]=='"': in_str=True; out.append(' '); i+=1; continue
        out.append(src[i]); i+=1
    return ''.join(out)

def main() -> int:
    p=argparse.ArgumentParser()
    p.add_argument('file', type=Path)
    p.add_argument(
        '--forbid', action='append', choices=['sorry','admit','native_decide'], default=None
    )
    p.add_argument('--forbid-declarations', default=None)
    a=p.parse_args(); src=strip_comments_and_strings(a.file.read_text())
    # With no selector flags, run the complete strict benchmark policy.
    forbid = a.forbid if a.forbid is not None else ['sorry', 'admit', 'native_decide']
    decl_arg = a.forbid_declarations if a.forbid_declarations is not None else 'axiom,constant'
    bad=[]
    for tok in forbid:
        if TOKEN_PATTERNS[tok].search(src): bad.append(tok)
    if NATIVE_DECIDE_PATTERN.search(src):
        bad.append('decide-with-native-backend')
    if DISABLED_LINTER_PATTERN.search(src):
        bad.append('disabled-linter-or-warning-gate')
    decls=set(filter(None,(x.strip() for x in decl_arg.split(','))))
    for kind,name in DECL_PATTERN.findall(src):
        if kind in decls: bad.append(f'{kind}:{name}')
    if bad:
        print('forbidden constructs: '+', '.join(bad), file=sys.stderr); return 1
    return 0
if __name__=='__main__': raise SystemExit(main())
