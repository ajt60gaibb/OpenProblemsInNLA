# PF-05: independent common-chart and conic-classification review

Reviewer: independent statement/zero-branch agent (`fr05_statement`). Date: 2026-10-18.

Verdict: **APPROVE the four gates below.** The fresh isolated 23-source build and 15-constant kernel consumer both passed; every live source remained byte-identical. This review is not a full-target or Linux Comparator claim.

## Reviewed immutable source bytes

| Module under `lean-statements/NLA/Proofs/PF05/` | SHA-256 |
| --- | --- |
| `CommonChart.lean` | `624ec5f89eefa476c433eefd6b7816e58ba8f02e8d885b393e5d820427521e1e` |
| `ConicDeterminant.lean` | `f640f126f051f07ae68c5e7ea4d23fc872d5a57275a384019835889d2a01e514` |
| `ConicPositive.lean` | `e3a8c8493d29d326dceea70eeb1bd3d00c91fdfef1c42863cd76982d898fe91b` |
| `ConicCongruence.lean` | `73f46bb8227cece8c2c21f40109ba726095176b41a664ee08488c26768d725d6` |

`CommonChart` was authored by the other solver; the three conic modules were authored by the root agent. I read all four complete sources. I authored the zero-normal-form and quartic-contact prerequisites, so their mathematical implementation is explicitly **excluded from this review's independent authorship coverage**. Rebuilding them as dependencies does not convert self-review into independent review. Their separate reviewers provide that coverage.

## Exact obligations and source assessment

`CommonChart.exists_common_chart` starts with the actual finite nonzero PSD families and constructs one actual invertible size-two matrix. Every transformed primal 00 entry and dual 11 entry is strictly positive. It does not assume factors are definite, nor that singular directions already lie in an affine chart. Its primal and dual quadratic polynomials have the correct shear signs. At least one strictly positive original diagonal proves each polynomial nonzero. The finite product is a nonzero real polynomial, so an actual common nonroot exists; PSD diagonal nonnegativity turns each nonzero transformed entry into a strict inequality. The construction includes empty families and singular factors. Both sides use the same determinant-one shear and the actual inverse-dual congruence.

`ConicDeterminant` assumes exactly that the actual coordinate action sends every homogeneous outer product to a singular matrix. Five actual evaluations recover the five conic equations. Those equations give determinant preservation on every symmetric matrix up to the displayed scalar, and the exact quadratic-form matrix identity in the retained `(a,c,b)` coordinates. Taking its determinant gives `scale^3 = det(L)^2`; invertibility therefore makes the actual scale positive. The sign is derived algebraically, with no omitted connectedness or punctured-plane assumption.

`ConicPositive` uses an actual positive definite matrix and its actual positive definite image to choose the positive cone component. The polar determinant at a nonzero outer product is the positive quadratic form at its rotated vector. Consequently every outer-product image is PSD; the same argument gives inverse primal positivity. The actual trace pairing then gives positivity of the weighted inverse-dual map. The input positive matrices are explicit hypotheses of these reusable intermediate lemmas, and are derived from the two actual factor families in the final classification wrapper.

`ConicCongruence.operator_congruence` constructs a fixed genuine four-by-three PSD factorization and proves its rank is three by an explicit nonsingular minor. The proved primal and inverse-dual positivity supply a genuine alternative factorization. Applying the actual zero-pair normal form and the four literal rank-one row tests forces its parameters to be `alpha=beta=0`, `gamma=1`. Actual full row span identifies the entire coordinate operator with the constructed congruence operator. This does not infer an arbitrary matrix operator from only one or two test vectors.

`congruent_of_conic_alternative` consumes two actual rank-three factorizations and their actual primal coordinate map. Its positive aggregate and positive image come from the actual factor sums. It returns the exact retained `Congruent A At B Bt` relation in original coordinates. The dual conclusion is derived by the actual trace separation of the alternative factors. No positivity-cone oracle, local-rigidity premise, closed-orbit premise, connected-quotient premise, or external theorem asserting the target is imported.

## Scope and remaining assembly

These gates preserve the canonical PF-05 target and original coordinates. Together with independently reviewed quartic obstruction, finite chart, and retained positive-ray compression, they support the strictly positive forward branch. The zero-entry branch and unrestricted reverse branch remain distinct assembly dependencies. This is an elementary direct conic/quartic adaptation of the campaign's proof route; it does not claim formalization of the manuscript's local analytic curve-selection or quotient-connectedness argument.

Fresh isolated evidence: `conic-chart-review-2-evidence/` beside this report. The audit snapshots the entire actual import closure, compiles into private objects with no shared NLA proof objects, checks selected exported constants in LeanCert kernel mode, prints axioms, and verifies live source bytes still match the snapshot. The result file records PASS for all 23 source commands and the 15-constant consumer; printed closure uses only `propext`, `Classical.choice`, and `Quot.sound`. Source snapshots use a `.txt` suffix in the retained evidence to distinguish review inputs from project sources. Linux CI and Comparator evidence remain separate required checks before promoting PF-05 as Lean-verified.
