#!/usr/bin/env python3
"""Keep canonical README mathematics safe from GitHub's Markdown parser.

Run with --write to normalize the registered pages, or --check (the default)
to report pages needing normalization. Optional arguments are permanent IDs.
Only math delimiters, equivalent operator typography, and three historical
PDF-only layout directives are changed. Code and ordinary prose are retained.
"""

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
FENCE = re.compile(r"^([ \t]*)(`{3,}|~{3,})([^\n]*)\n", re.M)
OPERATOR = re.compile(r"\\operatorname\{([A-Za-z]+)\}")
PDF_ONLY = {
    "MF-22": r"\pagestyle{plain}",
    "RA-12": r"\newpage",
    "RA-13": r"\newpage",
}


@dataclass(frozen=True)
class MathSpan:
    start: int
    end: int
    display: bool
    body: str
    indent: str = ""


def escaped(text, pos):
    start = pos
    while start and text[start - 1] == "\\":
        start -= 1
    return (pos - start) % 2 == 1


def display_body(body, indent):
    lines = body.split("\n")
    while lines and not lines[0].strip():
        lines.pop(0)
    while lines and not lines[-1].strip():
        lines.pop()
    return "\n".join(line.removeprefix(indent) for line in lines)


def math_spans(text):
    """Find dollar/protected/fenced math, skipping ordinary Markdown code."""
    i = 0
    while i < len(text):
        fence = FENCE.match(text, i)
        if fence:
            indent, marker, language = fence.groups()
            close = re.search(r"^[ \t]*" + re.escape(marker[0]) +
                              "{" + str(len(marker)) + r",}[ \t]*(?=\n|$)",
                              text[fence.end():], re.M)
            if not close:
                raise ValueError("Unclosed code fence")
            start = fence.end() + close.start()
            end = fence.end() + close.end()
            if language.strip() == "math":
                body = display_body(text[fence.end():start], indent)
                yield MathSpan(i, end, True, body, indent)
            i = end
            continue
        if text[i] == "`" and not escaped(text, i):
            marker = re.match(r"`+", text[i:])[0]
            end = text.find(marker, i + len(marker))
            i = len(text) if end < 0 else end + len(marker)
            continue
        if text[i] != "$" or escaped(text, i):
            i += 1
            continue
        if text.startswith("$`", i):
            end = text.find("`$", i + 2)
            if end < 0:
                raise ValueError("Unclosed protected inline math")
            yield MathSpan(i, end + 2, False, text[i + 2:end])
            i = end + 2
            continue
        if text.startswith("$$", i):
            end = i + 2
            while True:
                end = text.find("$$", end)
                if end < 0:
                    raise ValueError("Unclosed display math")
                if not escaped(text, end):
                    break
                end += 2
            line_start = text.rfind("\n", 0, i) + 1
            indent = text[line_start:i]
            if indent.strip():
                indent = ""
            body = display_body(text[i + 2:end], indent)
            yield MathSpan(i - len(indent), end + 2, True, body, indent)
            i = end + 2
            continue
        # Literal prices are not mathematics. $200$ remains a math expression.
        if re.match(r"\$\d[\d,]*(?:\.\d+)?(?:\s|$)", text[i:]):
            i += 1
            continue
        end = i + 1
        while True:
            end = text.find("$", end)
            if end < 0 or "\n\n" in text[i:end]:
                break
            if not escaped(text, end) and not text[end - 1].isspace() and not (
                    end + 1 < len(text) and text[end + 1].isdigit()):
                break
            end += 1
        if end >= 0 and "\n\n" not in text[i:end] and not text[i + 1].isspace():
            yield MathSpan(i, end + 1, False, text[i + 1:end])
            i = end + 1
        else:
            i += 1


def safe_operators(body):
    # Unstarred operatorname uses operator spacing and side-positioned scripts.
    def replace(match):
        following = body[match.end():match.end() + 1]
        separator = " " if following and following in "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz" else ""
        return r"\mathop{\mathrm{" + match[1] + r"}}\nolimits" + separator
    result = OPERATOR.sub(replace, body)
    if r"\operatorname" in result:
        raise ValueError("Review this nonstandard operatorname argument manually")
    return result


def format_markdown(text, identifier=None):
    directive = PDF_ONLY.get(identifier)
    if directive:
        text = re.sub(r"^" + re.escape(directive) + r"\n", "", text, flags=re.M)
    pieces = []
    previous = 0
    for span in math_spans(text):
        pieces.append(text[previous:span.start])
        body = safe_operators(span.body)
        if span.display:
            left = text[:span.start]
            right = text[span.end:]
            before = "" if not left or re.search(r"\n[ \t]*\n$", left) else (
                "\n" if left.endswith("\n") else "\n\n")
            after = "" if not right or re.match(r"\n[ \t]*\n", right) else (
                "\n" if right.startswith("\n") else "\n\n")
            lines = "\n".join(span.indent + line for line in body.split("\n"))
            pieces.append(before + span.indent + "```math\n" + lines + "\n" +
                          span.indent + "```" + after)
        else:
            # Markdown code spans flatten soft line breaks; do so explicitly.
            body = re.sub(r"[ \t]*\n[ \t]*", " ", body)
            pieces.append("$`" + body + "`$")
        previous = span.end
    pieces.append(text[previous:])
    return "".join(pieces)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("ids", nargs="*")
    args = parser.parse_args()
    registry = json.loads((ROOT / "problem_ids.json").read_text())
    unknown = set(args.ids) - registry.keys()
    if unknown:
        parser.error(f"Unknown permanent IDs: {sorted(unknown)}")
    changed = []
    for identifier, relative in registry.items():
        if args.ids and identifier not in args.ids:
            continue
        path = ROOT / relative
        old = path.read_text()
        new = format_markdown(old, identifier)
        if new != old:
            changed.append(identifier)
            if args.write:
                path.write_text(new)
    print(f"{'Formatted' if args.write else 'Need formatting:'} {len(changed)} pages" +
          (": " + ", ".join(changed) if changed else ""))
    return int(bool(changed) and not args.write)


if __name__ == "__main__":
    raise SystemExit(main())
