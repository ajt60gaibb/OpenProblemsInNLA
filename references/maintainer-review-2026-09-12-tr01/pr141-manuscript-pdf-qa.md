# PR141 immutable manuscript PDF review

Reviewed PR head: `2c7655f234bbb3b3134133ebae34eb479e9469e1`.

External source: `yuningyang19/OpenProblemsInNLA_TR-01` at immutable commit
`ed21181197ac839eac95f549404f94e7e3aa6e10`, read from
`/private/tmp/nla-tr01-proof`. No external-source files were modified.

Verdict: **PASS for mathematical source correspondence and publication layout,
with an explicit stale formalization-disclosure exception.** The pinned PDF
must not be described as an exact rendering of the current TeX disclosure.
There is no mathematical theorem/proof difference identified. Kernel validation
and canonical PDF review belong to separate reviewers.

## Precisely isolated PDF/source differences

The immutable commit's parent is
`bec29c5783aa2b90b8f6fd3c59a410ea4a2ad662`. The PDF is byte-identical at these
two commits (Git blob `7cc3aed4a29da273897753790a37562f31dcfd1e`). The entire
`manuscript.tex` diff between them consists of exactly two prose changes:

1. Current TeX line 53 adds an abstract sentence saying that the mathematical
   statements and proofs have also been formalized in Lean 4. This sentence is
   absent from PDF page 1.
2. Current TeX lines 3158–3166 replace the acknowledgments' formalization status
   and companion link. PDF page 40 retains the parent text: the earlier
   selected-width version was formalized, and the present prescribed-width
   theorem/density extensions have not been included in that formalization.
   Current TeX instead says the present statements and proofs, including those
   extensions, have been formalized, describes independent correspondence and
   kernel checks, and links the present companion. The old link points to
   `rerandSRHT_prob_5_6_simons_workshop` commit
   `5fb87c321a65baeaac09c79458a7356944647116`; the new source link points to
   `OpenProblemsInNLA_TR-01/tree/main/lean`.

There are **no changes to theorem statements, hypotheses, definitions,
equations, proofs, constants, figures, or bibliography** in this source diff.
In particular, the PDF already contains the prescribed-width result, not just
the earlier existential-width result. The source's remaining file changes
concern repository metadata and Lean/audit material, not manuscript figures.

A canonical disclosure that says the pinned PDF's abstract/acknowledgments
predate the current formalization disclosure, and points to the exact pinned
TeX plus actual independent kernel evidence, accurately handles this issue.
Do not silently replace the immutable source artifact or claim its page 40
describes the current formalization status.

## Independent rendering and text correspondence

I exported the parent's TeX to scratch, then compiled it twice with local
pdfLaTeX and `-no-shell-escape`, using the unchanged source assets. Both the
pinned PDF and this independent rebuild have 42 letter-size pages. The only
build warning is that epstopdf shell escape is disabled; there are no overfull,
underfull, undefined-reference, or compilation-error diagnostics.

All pages were compared through `pdftotext` extraction:

- 38 of 42 pages have byte-identical extracted text.
- Pages 17, 18, and 38 differ only in extracted whitespace.
- Page 26 differs in the extraction order of underbrace captions/subscripts,
  while retaining the same non-whitespace character multiset. I rendered and
  visually compared both versions of this page. The paired-port formula,
  paired-edge formula, five-factor count `L^a L^(8a) L^(18a) L^(36a) L^(9a)
  = L^(72a)`, and the remaining text/formulas are the same. This is an
  extraction-order effect, not a mathematical difference.

The independent rebuild uses pdfTeX 1.40.29 rather than the pinned PDF's
1.40.26, and its binary metadata/serialization are not expected to be equal.
The correspondence argument is the whole-document text comparison, the
visual resolution of the only non-whitespace extraction difference, and the
exact two-hunk source diff described above.

Evidence: `pr141-manuscript-extracted.txt`,
`pr141-pdf-compare/parent.tex`, `parent.pdf`, `parent-extracted.txt`,
`text-comparison.json`, `parent.log`, and `parent-page-26.png` under this audit
directory.

## Visual QA scope

All 42 pinned-PDF pages were rendered at 90 dpi and visually inspected in
seven six-page overview sheets. This checked page completeness, margins,
continuations, headings, displays, figures, tables, and references. No blank
or truncated page, clipped mathematics, broken glyphs, or overlapping material
was identified. This is an all-page overview inspection, not a claim to have
read every glyph at full-page magnification.

Pages 2, 6, 9, 18, 26, 31, 35, 39, and 40 were additionally inspected as
individual pages, covering the target theorem; two-projection transfer;
trace/Bernoulli bounds; cumulant/XOR lemma; graph-count underbraces; weighted
partition bound; fixed-size sampling transfer; explicit constants/all-rank
completion; final probability bound and the stale acknowledgment. Page 26 of
the independent rebuild was also inspected at larger resolution. The overview
includes complete figures on pages 4 and 25 and tables on pages 23, 27, and 30.

Key formula correspondence includes the exact two-round Walsh/sign law and
`k=min(n,ceil(C*r/epsilon^2))` in Theorem 1 on page 2; the pointwise compensated
signed-trace inequality on page 6; arbitrary-density Bernoulli hypotheses on
page 9; the two-density coupling and saturation case on page 35; and
`K0=576*4^24`, `R0=2^20000`, `C=200R0+8196K0` plus failure at most 0.01 on
pages 39–40. These agree with the already independently audited TeX proof.

Renders: `pr141-pages/page-01.png` through `page-42.png` and
`pr141-pages/overview-1.png` through `overview-7.png`.

## Immutable identities

- PDF SHA-256:
  `d59526bce0e062093e254a7f3319363c2501061ed92caa258573a1540b025ef0`.
- TeX SHA-256:
  `fdfae5f25863860cf55ee8439c1f2f6dbcd6b3768585b83889d242943fafebb5`.
- Pinned PDF: <https://github.com/yuningyang19/OpenProblemsInNLA_TR-01/blob/ed21181197ac839eac95f549404f94e7e3aa6e10/manuscript.pdf>.
- Pinned TeX: <https://github.com/yuningyang19/OpenProblemsInNLA_TR-01/blob/ed21181197ac839eac95f549404f94e7e3aa6e10/manuscript.tex>.

This report does not substitute the manuscript's self-reported Lean status
for an independent rebuild or kernel replay.
