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


def fence_close(text, fence):
    marker = fence[2]
    close = re.search(r"^[ \t]*" + re.escape(marker[0]) +
                      "{" + str(len(marker)) + r",}[ \t]*(?=\n|$)",
                      text[fence.end():], re.M)
    if not close:
        raise ValueError("Unclosed code fence")
    return fence.end() + close.start(), fence.end() + close.end()


def code_span_end(text, start):
    """CommonMark code spans close with an equally long backtick run."""
    marker = re.match(r"`+", text[start:])[0]
    for close in re.finditer(r"`+", text[start + len(marker):]):
        if len(close[0]) == len(marker):
            return start + len(marker) + close.end()
    return None


def remove_pdf_directive(text, directive):
    """Remove standalone layout commands, retaining literal code examples."""
    code_ranges = []
    i = 0
    while i < len(text):
        fence = FENCE.match(text, i)
        if fence:
            _, end = fence_close(text, fence)
            code_ranges.append((i, end))
            i = end
        elif text[i] == "`" and not escaped(text, i):
            end = code_span_end(text, i)
            if end is not None:
                code_ranges.append((i, end))
                i = end
            else:
                i += len(re.match(r"`+", text[i:])[0])
        else:
            i += 1

    def replace(match):
        if any(start <= match.start() < end for start, end in code_ranges):
            return match[0]
        return ""

    return re.sub(r"^" + re.escape(directive) + r"\n", replace, text, flags=re.M)


def math_spans(text):
    """Find dollar/protected/fenced math, skipping ordinary Markdown code."""
    i = 0
    while i < len(text):
        fence = FENCE.match(text, i)
        if fence:
            indent, marker, language = fence.groups()
            start, end = fence_close(text, fence)
            if language.strip() == "math":
                body = display_body(text[fence.end():start], indent)
                yield MathSpan(i, end, True, body, indent)
            i = end
            continue
        if text[i] == "`" and not escaped(text, i):
            end = code_span_end(text, i)
            if end is None:
                # Adding the protected math backticks could turn this literal
                # run into an opening code delimiter and hide the new math.
                raise ValueError("Escape an unmatched literal backtick before formatting math")
            i = end
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
        # A number followed by whitespace can begin either a price or math.
        # Accept a valid first closing delimiter, e.g. $2 \\times n$, but do
        # not pair a price with a later formula across its opening delimiter.
        maybe_price = re.match(r"\$\d[\d,]*(?:\.\d+)?(?:\s|$)", text[i:])
        end = i + 1
        valid_end = False
        while True:
            end = text.find("$", end)
            if end < 0 or "\n\n" in text[i:end]:
                break
            if not escaped(text, end):
                valid_end = not text[end - 1].isspace() and not (
                    end + 1 < len(text) and text[end + 1].isdigit())
                if maybe_price and "`" in text[i + 1:end]:
                    valid_end = False
                if valid_end or maybe_price:
                    break
            end += 1
        if valid_end and not text[i + 1].isspace():
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


def safe_angles(body):
    # GitHub's HTML sanitizer can truncate even fenced math at <x or </x.
    # TeX ignores the added whitespace and retains the ordinary < relation.
    return re.sub(r"<(?=[A-Za-z/!?])", "< ", body)


def format_markdown(text, identifier=None):
    directive = PDF_ONLY.get(identifier)
    if directive:
        text = remove_pdf_directive(text, directive)
    pieces = []
    previous = 0
    for span in math_spans(text):
        pieces.append(text[previous:span.start])
        body = safe_angles(safe_operators(span.body))
        if span.display:
            left = text[:span.start]
            right = text[span.end:]
            before = "" if not left or re.search(r"\n[ \t]*\n$", left) else (
                "\n" if left.endswith("\n") else "\n\n")
            after = "" if not right or re.match(r"\n[ \t]*\n", right) else (
                "\n" if right.startswith("\n") else "\n\n")
            if span.indent:
                # GitHub leaves indented math fences as literal list code.
                # A standalone protected expression retains display style.
                body = re.sub(r"[ \t]*\n[ \t]*", " ", body)
                if not re.match(r"\\displaystyle(?:\s|[^A-Za-z]|$)", body):
                    body = r"\displaystyle " + body
                pieces.append(before + span.indent + "$`" + body + "`$" + after)
            else:
                pieces.append(before + "```math\n" + body + "\n```" + after)
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
