# IE-19 statement and numerical obligations

Statement draft prepared before proof implementation, 12 September 2026.
Formalization author: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. The counterexample and its informal proof are due to Matthew J. Colbrook; their attribution remains in the canonical entry and source manuscript. AI assistance is used for the formalization. No human review or completed Lean verification is asserted at this stage.

The source of truth is the original Problem statement in `../README.md`, pinned at upstream commit `5adea969c17391693978ada2674d25bb5c3daeb1`. The mathematical source is Section 1 of `references/colbrook-recovered-2026-09-11/manuscripts/IE-19.tex` at that same commit.

## Exact formal target

`NLA.IE19.SharpConjecture` retains every original universal quantifier: natural dimension n≥3; real m>0 and α≥(n−2)m; every real symmetric J with strictly positive entries bounded entrywise by S=αI+m11ᵀ and weak diagonal dominance. It asserts the displayed lower bound and equality exactly for J=S. There is no extra hypothesis that J is strictly diagonally dominant or invertible. The witness will be proved invertible explicitly, so totalized matrix inversion cannot create the counterexample.

`NLA.IE19.rowSumNorm` is the maximum of the sums of absolute values in each row. Its implementation takes the finite supremum in nonnegative reals and then coerces to reals; it does not use the default entrywise matrix norm. At positive n it is exactly the canonical norm. Row/column positions use Fin n, starting at zero, without changing the ordering or the matrix entries.

The comparator exports (1) a fully admissible strict counterexample with actual matrix inverses and exact norms, (2) the negation of the inequality alone, and (3) the negation of the full equality-characterized conjecture. Proving (3) settles the entire original yes/no question negatively. The later sharp-infimum replacement in Colbrook's manuscript is additional mathematics and is not claimed formalized by this project.

## Frozen numerical obligations

All quantities below are exact rationals interpreted in the reals. No floating-point data or interval covering is needed.

1. n=3, α=m=1 meet n≥3, m>0, α≥(n−2)m. The comparison matrix S has diagonal 2 and all off-diagonal entries 1.
2. J has diagonal 2 and all off-diagonal entries 1/2. Verify symmetry, 0<J_ij≤S_ij for all nine entries, and the three weak dominance inequalities. The witness also happens to be strictly dominant; the conjecture is not restricted to that case.
3. K has diagonal 5/9 and all off-diagonal entries −1/9. Verify J K=I (and/or K J=I), prove nonsingularity, and derive J⁻¹=K using the standard matrix inverse.
4. T has diagonal 3/4 and all off-diagonal entries −1/4. Verify S T=I, prove nonsingularity, and derive S⁻¹=T.
5. Every absolute row sum of K equals 7/9; every absolute row sum of T equals 5/4. Verify the finite maxima, not merely a bound on a selected entry or row.
6. The displayed comparison expression at these parameters equals 5/4. Certify the strict scalar inequality (7:ℝ)/9<5/4 with LeanCert in explicit kernel mode.
7. Instantiate the universal conjectures at this admissible J and derive both negations from the strict inequality.

Algebraic simplification and exact finite sums/matrix products precede the single scalar numerical check. There are no interval subdivisions, transcendental approximations, or hidden asymptotic bounds. Only `propext`, `Classical.choice`, and `Quot.sound` may occur transitively; a subset is acceptable. Proof implementation must wait until the definitions and target declarations pass statement review. Subsequent changes to them require re-review before the implementation or verification is considered current.
