# Scoped cross-module mathematical and Lean review

Verdict: **PASS for the four modules listed below**.

Reviewer: the `choose_tensors` Codex agent, 28 September 2026. This is an
AI-agent review, not human peer review. I did not author or edit the reviewed
modules. I authored the Prony/upper-bound modules and `Lower.lean`; those files,
the final solution assembly, packaging, and the complete repository verification
procedure are explicitly outside this independent review scope. This report
does not constitute two independent reviews of the complete project.

## Exact reviewed sources

| Source | SHA-256 |
|---|---|
| `NLA/TR13/MatrixCertificate.lean` | `a94e4eb3185101220c8a8192bb3beb2a3ff8fcfadf35f9267f47fc83ccb6b491` |
| `NLA/TR13/LowerRank.lean` | `bf7afd3d2b04ea9daf42aa54260f1ba8f0f1e7da49e091d0c4b4e07582410602` |
| `NLA/TR13/Compression.lean` | `a3c3ae15b0a4c0c1585bd2314a994a54f2b27e0cbc0cdf32447470647025702b` |
| `NLA/TR13/RankComparison.lean` | `555d6e6ee61f29a4ddc3c199a1ee9ab71ea6a132961f92d2ce352a9817fdd6e3` |

## Mathematical findings

`MatrixCertificate` constructs its determinant certificate from a genuine
matrix rank normal form. Its fixed changes of basis and selected submatrix
retain the implication from nonzero determinant to the original matrix-rank
lower bound. The limit argument uses continuity of this determinant and
uniqueness of limits. It makes no boundedness or convergence assumption about
factorizations. The multivariate certificate is proved nonzero by evaluation
at its actual witness.

`Compression` constructs a coordinate representative for every admissible
index sum. The grouped indices cover precisely the original `2*k+1` factors,
and the product identity proves preservation of pure tensors. The selected
middle coordinates are in range. For `n=2` they coincide; neither the
definition nor the preservation proof assumes they are distinct. The Hankel
entry identity matches the original sum of zero-based tensor indices.

`LowerRank` applies a fixed linear and continuous coordinate map to the full
ambient tensor space. Its ordinary-rank bound therefore covers arbitrary
unstructured decompositions. The border argument applies to arbitrary
entrywise convergent ambient sequences and introduces no symmetry condition.
The polynomial evaluation identity specializes exactly to that same
flattening. The witness-to-open-set theorem preserves the required factor of
two in both matrix-rank bounds.

`RankComparison` absorbs a symmetric summand's scalar into one actual tensor
factor, using the explicit positive-order hypothesis. The constant-sequence
and sequencewise inclusions establish the necessary border comparisons.
Although the rank definitions use natural-number infima, every rank set in
the conclusion receives an actual member from the Vandermonde upper bound;
the proof does not rely on the value of an infimum of an empty set. The
nonemptiness proof for the principal open set uses polynomial extensionality
over the infinite field of complex numbers.

No mathematical or statement mismatch was found within this scope.

## Local verification

The audit ran on macOS 26.6.2, Apple ARM, using Lean 4.33.1. The exact command
and output are retained in
`verification/cross-module-macos-axioms.log`; the audit declarations are in
`verification/cross-module-audit.lean`.

All nine audited declarations compiled and reported only `propext`,
`Classical.choice`, and `Quot.sound`. A token scan of the four reviewed sources
found no `sorry`, `axiom`, or `admit`. No Linux build, sandboxed exporter,
Comparator, or complete-project independent verification is asserted here.
