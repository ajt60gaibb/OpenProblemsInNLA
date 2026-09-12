# IE-02 independent publication-conversion review

Reviewer: root Codex agent, separate from the proof author and packaging agent.
Date: 11 September 2026 (UTC).

**PASS.** This review checks publication conversion and the exact canonical scope. The complete independent mathematical review remains separately preserved, unchanged, in [IE-02-independent-review.md](IE-02-independent-review.md). This is automated-agent review, not human peer review or formal certification.

I read the complete final Markdown proof, its canonical notice, the resolution entry, the independent mathematical report, and the exact source-checker implementation. I independently compared the source's mathematical Sections 1–5 against the publication text: the 9,153-byte core is identical after removing only the five explicit Needspace and 21 nopagebreak directives. There is no mathematical amendment, changed quantifier, additional assumption, or omitted proof step. The preliminary research-status section is replaced by accurate publication metadata; the full original remains archived byte for byte.

I reran the source checker successfully. It compares all 157 ordered inline and displayed mathematical expressions in the generated standalone TeX. Its frozen source hash is `64bbb398344d56651a1a59c65613817bc932cea6772483893a5fc195ce3d9fb9` and the mathematical-review hash is `5a7f2e3b9f28d16566da3e51046434c889ad7cec686ad083e6250597fc951e6c`. I separately compared the canonical text from Problem statement through the final historical audit against upstream `87366c62d3b5c47d170f747b1cb40ab38d501013`; that entire suffix is unchanged.

The new notice accurately states equality for all n≥2, every 1≤k<n, and every nonzero complex eigenvalue, with complex polynomials and starting vectors. Theorem 6 is explicitly a triangular-Toeplitz affine result. The maximal singular-space and scalar-factorization steps apply without a simplicity restriction. The external Carathéodory–Fejér input is precisely attributed; the new proof is not attributed to its background references. The author's name, university and department appear in the manuscript, canonical record and RESOLVED entry. No contact email appears in the new documents or either PDF.

I visually inspected all five final solution pages and both final canonical pages using their rendered page images. All mathematical displays, proof conclusions, references and attribution are readable; there is no clipping, overlap, missing glyph, cut-off table, or orphaned display introduction. The optional-email template conditional and IE-02 reference-section page break are limited to document rendering and do not alter the proof. The packaging record separately documents successful two-pass XeLaTeX builds, the 203-ID safeguards, all 17 tests and checked local links.

The issue and PR drafts identify the exact target, affirmative result, theorem locator, author/affiliation, independent automated review, historical ratings and public-eligibility evidence. Root will bind their links to the final published commit and insert the related issue before creating the PR. No upstream acceptance or first-discovery claim follows from this review.

## Frozen canonical artifacts reviewed

| File | Bytes | SHA-256 |
|---|---:|---|
| `README.md` | 4097 | `00995b51b7721dba9b969c26d19ebdbf4b9ac494ddc087aef498b570e2ca781d` |
| `solution.md` | 12737 | `9c9673bdd1e9324c0b4b84519e4691724de67e046b8c17ff3882686cb699d2f9` |
| `solution.tex` | 15028 | `c3bd715724ebd12f95ab75c6b63d420c2efd3132d2e600e4f4e774ee49b8e52a` |
| `solution.pdf` | 76257 | `5c43422fdc05e7cb93862eefb271454988135082976da7a030c61d0044057f2d` |
| `problem.tex` | 7479 | `bdd718a5ea1ffebc2c6b520220555097d9d54a61b4171141bda7ae00bfdb3419` |
| `problem.pdf` | 38562 | `528cef7f597c859c7f3c942d1ea3ca55c227c6691e2a589a8801d0d01c46b464` |
