# PF-05 independent signed-quartic, contact and conic source approval

Reviewer: `/root/solved_inventory`, independent of the authors of the nine files below, 18 October 2026. APPROVE the exact supporting statements in these files. This report is not approval of the complete PF-05 assembly, canonical package, or Linux Comparator evidence.

The complete nine sources were read. The signed-polynomial construction repairs only the actual zero nodes of a given nonzero weakly signed polynomial. Distinct nodes bound their number by its degree. Lagrange interpolation at precisely those nodes stays within the original degree bound, and a common positive perturbation preserves the finitely many already strict signs. At a repaired node the signed perturbation is a positive multiple of the square of its nonzero sign. Empty node sets are included. No interpolation or separation oracle is supplied.

The determinant formulas use the actual row coordinates `(a,c,b)` and weighted dual coordinates `(d,f,2e)`. The primal determinant derivative is the displayed quartic; the derivative of the negative dual action at its trace-orthogonal dual chart is its negative. The factor two, opposite sign, and explicit quartic realization are correct. StrictPSD derives actual straight PSD segments including time zero: positive trace persists; the singular determinant is time multiplied by a function positive near zero; definite determinants remain positive. Finite intersection gives one positive interval for both full families. Trace cancellation is the exact weighted identity. Rank-three row spans show that a common scalar action forces the whole direction polynomial to vanish.

ActualContactChart retains original factor indices. Positive selected diagonal entries yield exact singular-factor charts with positive scales. The inverse-dual identity is derived from the two actual rank-three factorizations. Same-side contact equality is equivalent here to a positive-ray equality, excluded by the explicit distinct-ray hypotheses. Cross-side equality forces an actual zero trace entry, contradicted by strict positivity of M. These hypotheses remain explicit in this supporting gate; they are not assumptions of the frozen problem statement.

PositiveQuartic obtains all actual weak signs: primal alternative determinants are nonnegative, while a dual contact is trace-orthogonal to its nonzero PSD alternative dual factor, forcing the primal image determinant nonpositive. This argument derives nonzeroness and the dual identity from actual data, and requires no determinant-L or orbit premise. Strictification gives a realizable nonzero quartic with strict actual signs. Its exact coordinate action is a genuine feasible direction for all factors. Frozen straight rigidity and the actual row span then force that nonzero polynomial to vanish, a contradiction.

The homogeneous bridge handles the projective point at infinity by the fourth coefficient. Thus zero affine quartic forces the determinant of every actual rank-one image to vanish, without discarding a projective direction.

ConicDeterminant proves the full determinant quadratic form scales by its actual coefficient. Its metric identity yields scale-cubed equal to determinant-squared, so an invertible operator has strictly positive scale. ConicPositive uses an actual positive definite aggregate and its positive definite image to select the positive cone component, proves inverse-primal positivity, and derives inverse weighted-dual positivity by actual trace pairing against outer products. These are genuine consequences, not an assumed cone-preserver representation.

ConicCongruence uses a fixed actual 4-by-3 PSD factorization of ordinary rank three. The already proved zero-pair normal form applies to its actual primal/inverse-dual images. Singularity of the four displayed rank-one images forces the canonical parameters alpha=beta=0 and gamma=1 (gamma is actually positive). The four spanning rows then identify the entire actual coordinate operator with a genuine invertible congruence. For arbitrary actual alternatives, both positive aggregate hypotheses are derived from rank-three factorizations; trace nondegeneracy restores every dual factor in original coordinates. No local-rigidity, closed-orbit, connected-quotient, differentiable-choice, or conic-classification oracle occurs.

## Independent fresh kernel evidence

Both audits snapshot the entire local import closure, build every source into a newly created empty output directory using only read-only pinned dependency objects, and compile a generated consumer that verifies every explicit declaration, theorem declaration kind, kernel trust, and axioms. Campaign NLA objects are not on the Lean path. Source bytes were checked unchanged after each build. Raw source snapshots, consumer, commands, logs, dependency revisions and driver snapshots are retained in the evidence directories.

- `quartic-and-conic-review-1-evidence/result.json`: PASS, 28 actual source/consumer commands, 295 explicit declarations, 227 theorem/lemma-kind checks. Receipt SHA-256 `35d15c2aee0c9026064472946562bb3f39fc2fbeeb5d90a8ffbea34e0b1c7363`.
- `positive-quartic-review-1-evidence/result.json`: PASS, 15 actual source/consumer commands, 178 explicit declarations, 142 theorem/lemma-kind checks. Receipt SHA-256 `6d91f5f629b449f6cfde5e4a3e7b30227862b44670fcad9cf8c10a12c94c77f4`.

Every audited declaration is accepted in LeanCert kernel mode with only the foundational axioms `propext`, `Classical.choice`, and `Quot.sound`. This is local kernel evidence; authoritative Linux/Comparator checks remain separate.

Authorship boundary: the reviewer authored imported CoordinateActions, PSDLine, InfinitesimalOperator, OperatorFactorization and CongruenceLine prerequisites (and other reverse/core/chart modules outside this supporting scope). Those were rebuilt and checked transitively, but are explicitly excluded from this review's independent source approval. The reviewer authored none of the nine approved files below. No proof source was edited during review.

| Independently reviewed source | SHA-256 |
|---|---|
| `PolynomialStrictification.lean` | `fe432727f9faeb504b66bfa3fa141e4f49b6e5d3341c9a9185aeac01c351b305` |
| `ContactQuartic.lean` | `f1b6fdf69cbd305fe5f75716cf08e5771e6ac8945db10d952f947467d687f968` |
| `StrictPSD.lean` | `e6d6bc3057e55eb83cd97c8adaa109bab5c5e9b8f7a84fd2ebaeea862631a750` |
| `HomogeneousQuartic.lean` | `939be750d6d85381b55ca480534745e07a5d1aeb59f137f2fb7a26e5678acdad` |
| `ActualContactChart.lean` | `2b1f1b91e48c82e232e64e7f1b58da15f01d8ef6b3e2406395b5563bec05c5ed` |
| `PositiveQuartic.lean` | `9eb60fbd83b9b727de6d60e1d3d50f7a7ef2efcaaa3d8e6a9c2e2cce3716bc92` |
| `ConicDeterminant.lean` | `f640f126f051f07ae68c5e7ea4d23fc872d5a57275a384019835889d2a01e514` |
| `ConicPositive.lean` | `e3a8c8493d29d326dceea70eeb1bd3d00c91fdfef1c42863cd76982d898fe91b` |
| `ConicCongruence.lean` | `73f46bb8227cece8c2c21f40109ba726095176b41a664ee08488c26768d725d6` |
