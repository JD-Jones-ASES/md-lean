#!/usr/bin/env python3
# -*- coding: ascii -*-
"""Reject proof placeholders in Span/ and Solution.lean.

Challenge.lean may contain intentional sorry. Kernel-bypass options
are forbidden everywhere.
"""
from __future__ import print_function

import re
import sys
from pathlib import Path

FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|axiom|unsafe|partial|native_decide|implemented_by|extern)\b"
    r"|\bLean\.ofReduceBool\b|\bdebug\.skipKernelTC\b|\bdebug\.byAsSorry\b"
)
KERNEL_BYPASS = re.compile(r"\bdebug\.skipKernelTC\b|\bdebug\.byAsSorry\b")


def code_without_comments_or_strings(source):
    result = list(source)
    index = 0
    depth = 0
    in_string = False
    while index < len(source):
        pair = source[index:index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                result[index:index + 2] = "  "
                index += 2
            elif pair == "-/":
                depth -= 1
                result[index:index + 2] = "  "
                index += 2
            else:
                if source[index] != "\n":
                    result[index] = " "
                index += 1
        elif in_string:
            if source[index] == "\\":
                result[index] = " "
                index += 1
                if index < len(source):
                    if source[index] != "\n":
                        result[index] = " "
                    index += 1
            else:
                if source[index] == '"':
                    in_string = False
                if source[index] != "\n":
                    result[index] = " "
                index += 1
        elif pair == "/-":
            depth = 1
            result[index:index + 2] = "  "
            index += 2
        elif pair == "--":
            end = source.find("\n", index)
            if end < 0:
                end = len(source)
            result[index:end] = " " * (end - index)
            index = end
        elif source[index] == '"':
            in_string = True
            result[index] = " "
            index += 1
        else:
            index += 1
    if depth or in_string:
        raise ValueError("unterminated Lean comment or string")
    return "".join(result)


def violations(source, pattern):
    cleaned = code_without_comments_or_strings(source)
    out = []
    for match in pattern.finditer(cleaned):
        line = cleaned.count("\n", 0, match.start()) + 1
        out.append((line, match.group()))
    return out


def main():
    root = Path(__file__).resolve().parent.parent
    proof_files = sorted((root / "Span").rglob("*.lean"))
    proof_files.append(root / "Span.lean")
    proof_files.append(root / "Solution.lean")
    if not (root / "Solution.lean").is_file() or not (root / "Span").is_dir():
        print("Source guard requires Span/ and Solution.lean", file=sys.stderr)
        return 1
    failures = 0
    for path in proof_files:
        try:
            found = violations(path.read_text(encoding="utf-8"), FORBIDDEN)
        except (OSError, UnicodeError, ValueError) as error:
            print("%s: %s" % (path.relative_to(root), error), file=sys.stderr)
            failures += 1
            continue
        for line, token in found:
            print("%s:%s: prohibited proof token %s"
                  % (path.relative_to(root), line, token), file=sys.stderr)
            failures += 1
    challenge = root / "Challenge.lean"
    try:
        found = violations(challenge.read_text(encoding="utf-8"), KERNEL_BYPASS)
    except (OSError, UnicodeError, ValueError) as error:
        print("Challenge.lean: %s" % error, file=sys.stderr)
        failures += 1
    else:
        for line, token in found:
            print("Challenge.lean:%s: prohibited option %s" % (line, token),
                  file=sys.stderr)
            failures += 1
    if failures:
        return 1
    print("Source guard passed for %d proof files; Challenge checked for "
          "kernel-bypass options only." % len(proof_files))
    return 0


if __name__ == "__main__":
    sys.exit(main())
