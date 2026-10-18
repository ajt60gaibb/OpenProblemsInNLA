# Proof inventory for the 47 formerly Solved targets

This source-level inventory records the 47 targets that had `Solved` status
before the split proof campaign. The nine full-target proofs below now have
canonical `Lean verified` status after independent scope review and recorded
kernel verification. The remaining 38 retain `Solved` status. This inventory
alone does not certify a proof; each promoted canonical README records its
statement comparison, pinned source, successful verification log, and axiom
audit. Permanent IDs and mathematical targets are unchanged. Historical copies
under `reviews/`, `verification/`, and archive directories are evidence, not
live solution sources.

## Full-target local proofs promoted to Lean verified (9)

| ID | Live proof source | Evidence and remaining gate |
| --- | --- | --- |
| FR-05 | [`Solution.lean`](../../../frames-and-matrix-designs/FR-05/lean/Solution.lean) | Exports the original Gaussian/all-signals limit and the stronger `C/d` bound. Independent [source review](FR-05/INDEPENDENT_REVIEW.md) and the [isolated Linux Comparator/LeanCert kernel receipt](FR-05/LINUX_CI_RECEIPT.md) pass with only standard axioms. The separate `Challenge.lean` contains deliberate `sorry`s and is not imported by `Solution`. |
| TR-13 | [`Solution.lean`](../../../tensor-computations/TR-13/lean/Solution.lean) | Exports `NLA.TR13.generic_rank_equality` and the [independently reviewed all-width bridge](TR-13/EXACT_STATEMENT_INDEPENDENT_REVIEW.md) for every odd `m ≥ 5`, `n ≥ 2`, with all five exact generic ranks and equivalence at every natural width. The [isolated Linux Comparator/LeanCert kernel receipt](TR-13/LINUX_CI_RECEIPT.md) passes with only standard axioms. |
| MF-23 | [`CanonicalBridge.lean`](../../../matrix-functions-and-stability/MF-23/lean/CanonicalBridge.lean) | Proves the [reviewed canonical block-order target](MF-23/CANONICAL_BRIDGE_INDEPENDENT_REVIEW.md) from the pinned external `complete_crouzeix` proof by a norm-preserving tensor-factor swap. Its self-contained source-locked project and [isolated Linux Comparator/LeanCert kernel receipt](MF-23/LINUX_CI_RECEIPT.md) pass with only standard axioms. |
| RA-06 | [`Final.lean`](../../../lean-statements/NLA/Proofs/RA06/Final.lean) | The [independently reviewed full theorem](RA-06/FINAL_INDEPENDENT_REVIEW.md) inhabits the frozen original negative `Target` for every `p > 2`, with the exact sampler, same `α`, expected retained count, and raw log budget. The [isolated Linux Comparator/LeanCert kernel receipt](RA-06/LINUX_CI_RECEIPT.md) passes with only standard axioms. |
| MF-03 | [`AllOrderTarget.lean`](../../../lean-statements/NLA/Proofs/MF03/AllOrderTarget.lean) | The [independently reviewed full theorem](MF-03/ALL_ORDER_TARGET_INDEPENDENT_FINAL_REVIEW.md) inhabits the frozen all-order `Target`: reduced-pair existence and the radius-3, error-2 bound for every reduced representative at every positive Padé order. Orders 1–15 use audited finite certificates; orders ≥16 use the source determinant-derived symbolic pair and coefficient-one tail. The pinned aggregate LeanCert kernel build passes with only standard axioms. |
| RA-10 | [`Solution.lean`](../../../randomized-and-low-rank-approximation/RA-10/lean/Solution.lean) | The [two independent final source reviews](../../../randomized-and-low-rank-approximation/RA-10/lean/reviews/FINAL_FORMALIZATION_REVIEW_1.md) and [isolated Linux Comparator/LeanCert kernel receipt](RA-10/LINUX_CI_RECEIPT.md) verify the complete frozen existential target with universal witness 11, arbitrary PSD pair and selected eigenbases, all admissible operator-monotone functions, and only standard axioms. The substantive 95-module proof closure is pinned to commit `844237f7`. |
| MD-03 | [`Proof.lean`](../../../matrix-discrepancy-and-optimization/MD-03/lean/NLA/MD03/Proof.lean) | Proves the complete universal signing target with C=36 through a pinned Komlós formalization. The [independent source review](MD-03/INDEPENDENT_REVIEW.md) and [isolated Linux Comparator/kernel receipt](MD-03/LINUX_CI_RECEIPT.md) pass with only standard axioms. |
| MD-04 | [`Proof.lean`](../../../matrix-discrepancy-and-optimization/MD-04/lean/NLA/MD04/Proof.lean) | Proves the complete square-root sparsity target with C=36 by rescaling 0–1 matrices into the pinned MD-03 Komlós theorem. The [independent source review](MD-04/INDEPENDENT_REVIEW.md) and [isolated Linux Comparator/kernel receipt](MD-04/LINUX_CI_RECEIPT.md) pass with only standard axioms. |
| SP-11 | [`Solution.lean`](../../../eigenvalues-and-inverse-problems/SP-11/lean/Solution.lean) | Proves the full frozen unrestricted real symmetric delta Target using actual shared-variable noncancellation and greedy relabeling. Independent [full source/package reviews](SP-11/README.md) and the [actual isolated Linux Comparator/LeanCert kernel receipt](SP-11/LINUX_CI_RECEIPT.md) pass with only standard axioms. The original page, TeX and PDF are archived byte for byte. |

The [17 October campaign inventory](../campaign-2026-10-17/inventory/README.md)
retains the original immutable snapshots and candidate evidence. MD-03, MD-04,
and RA-10 were subsequently merged into published main; SP-11 is promoted here.

## Complete proof awaiting canonical Linux verification (1)

| ID | Live proof source | Evidence and remaining gate |
| --- | --- | --- |
| SP-12 | [`Final.lean`](../../../lean-statements/NLA/Proofs/SP12/Final.lean) and [`Solution.lean`](../../../eigenvalues-and-inverse-problems/SP-12/lean/Solution.lean) | Proves the unchanged full real symmetric PSD/SAP target with nullity at least the actual chromatic number minus one, using actual Strong Delta factors, the nonedge Gram derivative, one-vertex extension and finite graph induction. [Independent statement/source reviews and local kernel evidence](SP-12/README.md) are retained. Fresh full-closure and canonical review evidence is recorded separately; actual committed-project Linux Comparator and its independent artifact audit remain required. Canonical status remains Solved. |

## Local partial solution projects (8)

| ID | Live source | What is actually proved |
| --- | --- | --- |
| IE-21 | [`Solution.lean`](../../../linear-systems-and-elimination/IE-21/lean/Solution.lean) | Zero vector and empty row-energy lemmas. The full target is an axiom and the spherical-row law semantics remain unimplemented. |
| IE-22 | [`Solution.lean`](../../../linear-systems-and-elimination/IE-22/lean/Solution.lean) | Zero vector and empty row-energy lemmas. The full target is an axiom; complete semantics and proof remain. |
| IV-02 | [`Solution.lean`](../../../intervals-and-absolute-value-equations/IV-02/lean/Solution.lean) | Rotation identity and positive even layer count. The original complexity claim remains absent from the implemented semantics. |
| IV-04 | [`Solution.lean`](../../../intervals-and-absolute-value-equations/IV-04/lean/Solution.lean) | A two-by-two corner algebra lemma. The original complexity target is absent and the current statement's interval semantics have a known scope gap. |
| MD-06 | [`Solution.lean`](../../../matrix-discrepancy-and-optimization/MD-06/lean/Solution.lean) | Extracts a nonsynchronized critical point from an assumed stable event. Graph probability and local-minimum semantics are parameters of an abstract structure. |
| SP-14 | [`SubsequenceGap.lean`](../../../lean-statements/NLA/Proofs/SP14/SubsequenceGap.lean) | [Independently reviewed](SP-14/SUBSEQUENCE_GAP_INDEPENDENT_FINAL_REVIEW.md) kernel proof that a supplied continuous counterexample with a positive eventual empirical gap refutes the exact frozen conjecture. Separate [base-coefficient convolution](SP-14/BASE_COEFFICIENT_INDEPENDENT_REVIEW.md), [unconditional coefficient-defined block product](SP-14/BASE_CB_INDEPENDENT_FINAL_REVIEW.md), [frozen-integral monomial Fourier orthogonality](SP-14/BASE_FOURIER_MODE_INDEPENDENT_REVIEW.md), [absolute summability of the exterior half-binomial coefficients](SP-14/BASE_COEFF_SUMMABLE_INDEPENDENT_REVIEW.md), [continuous exterior boundary series](SP-14/BASE_EXTERIOR_SERIES_INDEPENDENT_REVIEW.md), [termwise frozen Fourier integration](SP-14/BASE_EXTERIOR_FOURIER_INDEPENDENT_REVIEW.md), [the exterior base symbol's exact Fourier pattern and actual odd Toeplitz characteristic polynomial](SP-14/BASE_EXTERIOR_PATTERN_INDEPENDENT_REVIEW.md), [its boundary square and zero identities](SP-14/BASE_EXTERIOR_BOUNDARY_SQUARE_INDEPENDENT_REVIEW.md), [positive packet Fourier support and small-section invisibility](SP-14/POSITIVE_PACKET_INVISIBILITY_INDEPENDENT_FINAL_REVIEW.md), [finite negative-restoration algebra and earlier-section persistence](SP-14/NEGATIVE_RESTORATION_INVISIBILITY_INDEPENDENT_FINAL_REVIEW.md), [the conditional all-order odd-frequency Toeplitz characteristic polynomial in the jet coordinate](SP-14/ODD_FREQUENCY_TOEPLITZ_CHARPOLY_INDEPENDENT_FINAL_REVIEW.md), [continuous odd Fourier support and jet polynomial shape for every finite corrected symbol](SP-14/FINITE_CORRECTED_ODD_SUPPORT_INDEPENDENT_FINAL_REVIEW.md), [the exact conditional jet-to-algebraic-root-multiplicity bridge](SP-14/JET_VANISHING_MULTIPLICITY_INDEPENDENT_FINAL_REVIEW.md), [the real upper-triangular base-jet matrix with its unique inverse solve](SP-14/BASE_JET_TRIANGULAR_INDEPENDENT_PARTIAL_REVIEW.md), and [the generic selected-block cofactor identity](SP-14/BASE_JET_CORNER_INDEPENDENT_FINAL_REVIEW.md), and [the exact frozen Fourier-to-matrix bridge for a base plus restored packet](SP-14/BASE_JET_FOURIER_MATRIX_INDEPENDENT_FINAL_REVIEW.md), and [the actual corrected odd-jet polynomial’s finite pencil formula](SP-14/BASE_JET_PENCIL_FORMULA_INDEPENDENT_FINAL_REVIEW.md), and [the explicit real first-jet solve and bijective derivative of that actual base-model map](SP-14/BASE_JET_REAL_SOLVE_INDEPENDENT_FINAL_REVIEW.md) are kernel checked. The base symbol has an outer annular extension and is not the counterexample; selecting correction vectors for perturbed backgrounds, the final infinite symbol, two-sided nonextension, unconditional multiplicity estimates, and final subsequence gap remain unproved in Lean. |
| TR-04 | [`Solution.lean`](../../../tensor-computations/TR-04/lean/Solution.lean) | Elementary candidate/window count inequalities. It explicitly does not prove the TT-SVD approximation target; the current statement has unconstrained rank and operation-count fields. |
| TR-14 | [`WidthBasics.lean`](../../../lean-statements/NLA/Proofs/TR14/WidthBasics.lean) | [Independently reviewed](TR-14/WIDTH_BASICS_INDEPENDENT_FINAL_REVIEW.md) kernel proofs of symmetric-width implies ordinary-width and both exact width-zero characterizations, [moment-index surjectivity and the Hankel-zero equivalence](TR-14/MOMENT_INDEX_INDEPENDENT_FINAL_REVIEW.md), [the exact apolar map and least nonzero degree](TR-14/APOLAR_MINIMAL_INDEPENDENT_FINAL_REVIEW.md), [conditional monic quotient all-moment matching](TR-14/NORMALIZED_QUOTIENT_INDEPENDENT_PARTIAL_REVIEW.md), [the normalized least-apolar quotient’s full Frobenius pairing](TR-14/FROBENIUS_MINIMAL_INDEPENDENT_FINAL_REVIEW.md), [the exact middle catalecticant rank in that monic chart](TR-14/MIDDLE_CATALECTICANT_INDEPENDENT_FINAL_REVIEW.md), and [the genuine homogeneous chart substitution, degreewise equivalence, multiplication, and inverse-dual pairing](TR-14/GL2_HOMOGENEOUS_INDEPENDENT_FINAL_REVIEW.md). The original-coordinate middle catalecticant rank and a conditional local CRT/Fourier symmetric upper width are now proved through independently reviewed GL₂ chart bridges below. The arbitrary ordinary-to-symmetric implication and full all-width target remain unproved. |

The [independently reviewed MF-03 dense-set cosine product](MF-03/COSINE_DENSE_PRODUCT_INDEPENDENT_FINAL_REVIEW.md)
identifies the factorial wave series with `cos(πw)` and proves convergence
of its finite cosine product when `sin(πw)≠0`. The [all-complex extension](MF-03/COSINE_ALL_COMPLEX_INDEPENDENT_FINAL_REVIEW.md)
now proves the exact positive-factor product value identity and finite-product
convergence for every complex argument. The [independently reviewed coefficient
transfer](MF-03/COSINE_COEFFICIENT_TRANSFER_INDEPENDENT_FINAL_REVIEW.md)
identifies every finite-subset elementary coefficient with the exact factorial
wave coefficient. Later audited gates below complete the original Padé
denominator bounds and all-order Target.

The [independently reviewed finite bidiagonal minor](MF-03/FINITE_BIDIAGONAL_MINOR_INDEPENDENT_FINAL_REVIEW.md)
identifies every finite rectangular and augmented determinant with the exact
minor of a product of the original factor matrices, uniformly in `N,m,j`,
including empty and endpoint shapes. The [independently reviewed Toeplitz/Cramer
gate](MF-03/PADE_TOEPLITZ_CRAMER_INDEPENDENT_FINAL_REVIEW.md) identifies the
original rectangular determinant with the high Padé system determinant and
proves its unnormalized Cramer equation. The [finite minor Cauchy–Binet
identity](MF-03/FINITE_MINOR_CAUCHY_BINET_INDEPENDENT_FINAL_REVIEW.md) is now
kernel checked for arbitrary real site matrices, including the empty minor.
The [literal finite valid-path chain expansion](MF-03/FINITE_PATH_CHAIN_INDEPENDENT_FINAL_REVIEW.md)
now identifies every bidiagonal-product minor with the exact descending-label
weighted sum, including empty cases. The later audited gates below close the
endpoint path/tableau transport, determinant positivity, and signed coefficient
ratios; the subsequent polynomial-pair gates complete the all-order Target.
The [independently reviewed one-factor minor](MF-03/FINITE_BIDIAGONAL_STEP_INDEPENDENT_FINAL_REVIEW.md)
proves that every ordered upper-bidiagonal minor has exactly its stationary or
advance product weight, with all nonidentity determinant permutations zero.
The later gates below close the endpoint path/tableau bijection.
The [independently reviewed finite endpoint gate](MF-03/FINITE_PATH_ENDPOINT_INDEPENDENT_FINAL_REVIEW.md)
identifies the original augmented determinant with the exact valid-chain sum
and proves the per-path advance counts `m+1` and `m` for every `j≤m`.
The [independently reviewed advance-label gate](MF-03/FINITE_PATH_LABELS_INDEPENDENT_FINAL_REVIEW.md)
records exact zero-based factor labels and proves their count equals the
endpoint displacement and augmented-tableau column length for every path.
The [independently reviewed path-weight identity](MF-03/FINITE_PATH_WEIGHT_INDEPENDENT_FINAL_REVIEW.md)
factors each literal valid-chain weight over those exact advance labels.
The [generic column-order lemma](MF-03/FINITE_COLUMN_ORDER_INDEPENDENT_FINAL_REVIEW.md)
equates rowwise weak increase with all lower-label prefix-count inequalities
for equal and one-extra-bottom-cell adjacent columns.
The [finite cut formulation](MF-03/FINITE_COLUMN_CUTS_INDEPENDENT_FINAL_REVIEW.md)
gives the equivalent exact suffix-count inequalities with allowance zero or
one according to the augmented column lengths.
The [literal valid-path cut gate](MF-03/FINITE_PATH_CUTS_INDEPENDENT_FINAL_REVIEW.md)
identifies each intermediate position with its start plus processed advance
labels and proves the exact adjacent noncollision inequality at every cut.
The [sorted-column gate](MF-03/FINITE_COLUMN_SORTED_INDEPENDENT_FINAL_REVIEW.md)
enumerates each exact advance-label set in increasing order and preserves
every cut count without relabeling factors.
The [column-system gate](MF-03/FINITE_COLUMN_SYSTEM_INDEPENDENT_FINAL_REVIEW.md)
packages exactly those original label sets, cardinalities, and every-cut
noncollision inequality from each literal valid path.
The [uniform-column sentinel gate](MF-03/FINITE_UNIFORM_COLUMNS_INDEPENDENT_FINAL_REVIEW.md)
adds a temporary `N` only outside short-column tableau cells, proves exact
suffix corrections, and derives weak rows for all sorted temporary columns.
The [sentinel-placement gate](MF-03/FINITE_UNIFORM_COLUMN_BOUNDS_INDEPENDENT_FINAL_REVIEW.md)
proves `N` is exactly each excluded short-column bottom value and every
original tableau cell label is `<N`.
The [forward tableau map](MF-03/FINITE_UNIFORM_TABLEAU_INDEPENDENT_FINAL_REVIEW.md)
fills exactly the original augmented Young diagram from sorted path columns,
with weak rows, strict columns, and every actual entry `<N`; the inverse and
weighted bijection remain open.
The [reverse tableau-column values](MF-03/FINITE_TABLEAU_UNIFORM_INDEPENDENT_FINAL_REVIEW.md)
recover actual entries on every original cell and use `N` only at an omitted
short-column bottom position; the label sets and inverse path remain open.
The [uniform and actual label sets](MF-03/FINITE_TABLEAU_UNIFORM_SETS_INDEPENDENT_FINAL_REVIEW.md)
have the exact `m+1` temporary length and original long/short cardinalities
after erasing only the excluded sentinel; cut conditions remain open.
The [reverse tableau cut gate](MF-03/FINITE_TABLEAU_UNIFORM_CUTS_INDEPENDENT_FINAL_REVIEW.md)
now derives the original one-gap noncollision inequality at every factor-label
cut from weak rows and exact sentinel erasure; the literal inverse path remains open.
The [tableau-to-column-system map](MF-03/FINITE_TABLEAU_COLUMN_SYSTEM_INDEPENDENT_FINAL_REVIEW.md)
packages these sentinel-free labels with the exact original lengths and
noncollision condition for every `j≤m`; the two-sided inverse remains open.
The [recovered uniform-column gate](MF-03/FINITE_TABLEAU_UNIFORM_INVERSE_INDEPENDENT_FINAL_REVIEW.md)
proves that reaugmentation and strict sorting of those exact labels reproduce
every original tableau uniform value; tableau equality remains open.
The [tableau round trip](MF-03/FINITE_TABLEAU_ROUNDTRIP_INDEPENDENT_FINAL_REVIEW.md)
now proves exact equality after conversion to the actual-label column system
and back, cellwise on the unchanged augmented shape; reverse system identity remains open.
The [reverse column-system round trip](MF-03/FINITE_COLUMN_UNIFORM_INVERSE_INDEPENDENT_FINAL_REVIEW.md)
recovers every original actual label set after the forward tableau map and
proves the second exact identity; the literal path-chain inverse remains open.
The [tableau/column-system equivalence](MF-03/FINITE_TABLEAU_COLUMN_EQUIV_INDEPENDENT_FINAL_REVIEW.md)
packages both exact inverse maps on the original augmented shape. The
[finite label-suffix recurrence](MF-03/FINITE_LABEL_SUFFIX_STEP_INDEPENDENT_FINAL_REVIEW.md)
counts every zero-based advance label exactly; the source-locked
[cut-reconstruction contract](MF-03/FINITE_COLUMN_CUT_RECONSTRUCTION_INDEPENDENT_PRE_REVIEW.md)
fixes the pending literal path inverse and factor order.
The [cut-position gate](MF-03/FINITE_COLUMN_CUT_POSITIONS_INDEPENDENT_FINAL_REVIEW.md)
constructs every original-site ordered row at every label cut. The
[cut endpoint and transition gate](MF-03/FINITE_COLUMN_CUT_ENDPOINTS_INDEPENDENT_FINAL_REVIEW.md)
recovers the literal original endpoint tuples and factor-indexed valid steps;
the [literal cut-path constructor](MF-03/FINITE_COLUMN_CUT_PATH_INDEPENDENT_FINAL_REVIEW.md)
assembles those steps into the original `FiniteValidPath`. Its
[first exact inverse](MF-03/FINITE_COLUMN_PATH_LEFT_INVERSE_INDEPENDENT_FINAL_REVIEW.md)
recovers every original actual label set from the reconstructed path; the
reverse path identity is specified in the
[independently reviewed inverse contract](MF-03/FINITE_COLUMN_PATH_INVERSE_INDEPENDENT_PRE_REVIEW.md).
The [cut-extensionality gate](MF-03/FINITE_COLUMN_PATH_CUT_EXT_INDEPENDENT_FINAL_REVIEW.md)
proves that all factor cuts determine a literal path and that the reconstructed
path visits exactly its prescribed cut rows.
The [literal path right inverse](MF-03/FINITE_COLUMN_PATH_RIGHT_INVERSE_INDEPENDENT_FINAL_REVIEW.md)
now proves that extracting actual labels and reconstructing the path recovers
every original intermediate row and the full chain. Together with the left
inverse, both directions of the path/column-system bijection are proved;
the [exact equivalence](MF-03/FINITE_COLUMN_PATH_EQUIV_INDEPENDENT_FINAL_REVIEW.md)
packages these maps. Composing it with the tableau/column-system equivalence
gives the literal path/tableau bijection.
The [original-cell set equality](MF-03/FINITE_TABLEAU_CELL_SET_INDEPENDENT_FINAL_REVIEW.md)
identifies each actual column label set with the original upper cells and
optional genuine bottom cell, excluding the temporary sentinel. Products
over actual labels now equal the product of precisely those original cells
in the [independently audited product gate](MF-03/FINITE_TABLEAU_COLUMN_PRODUCT_INDEPENDENT_FINAL_REVIEW.md).
The [pointwise path/tableau weight identity](MF-03/FINITE_PATH_TABLEAU_WEIGHT_INDEPENDENT_FINAL_REVIEW.md),
[finite weighted-sum reindexing](MF-03/FINITE_PATH_TABLEAU_SUM_INDEPENDENT_FINAL_REVIEW.md),
and [original finite augmented determinant/tableau equality](MF-03/FINITE_AUG_DET_TABLEAU_INDEPENDENT_FINAL_REVIEW.md)
now close the exact finite transport under the
[reviewed contract](MF-03/FINITE_WEIGHTED_TABLEAU_TRANSPORT_INDEPENDENT_PRE_REVIEW.md).
The [original finite rectangular determinant/tableau identity](MF-03/FINITE_RECT_DETERMINANT_TABLEAU_INDEPENDENT_FINAL_REVIEW.md)
handles the `j=0` specialization. The [coefficient-one finite determinant
tail bound](MF-03/FINITE_DETERMINANT_TAIL_INDEPENDENT_FINAL_REVIEW.md)
uses the exact `m≤k<N` cosine-factor tail and actual bottom length `j`.
The [original finite and infinite determinant tail bounds](MF-03/ORIGINAL_DETERMINANT_INFINITE_TAIL_INDEPENDENT_FINAL_REVIEW.md)
retain coefficient one and the exact infinite cosine-factor tail. Strict
positivity of the original infinite rectangular determinant is now proved
from a [fixed canonical tableau lower bound](MF-03/RECT_DETERMINANT_POSITIVITY_INDEPENDENT_FINAL_REVIEW.md).
The [exact original determinant ratio](MF-03/ORIGINAL_DETERMINANT_RATIO_INDEPENDENT_FINAL_REVIEW.md)
is nonnegative and bounded by `(cosineTail m)^j` with coefficient one.
The [original Cramer sign](MF-03/CRAMER_AUGMENTED_DETERMINANT_INDEPENDENT_FINAL_REVIEW.md)
and [normalized nonconstant coefficients](MF-03/PADE_NONCONSTANT_COEFFICIENTS_INDEPENDENT_FINAL_REVIEW.md)
now transfer that bound to each actual high-degree Padé coefficient and prove
the exact Toeplitz system. The [exact denominator](MF-03/PADE_DENOMINATOR_POLYNOMIAL_INDEPENDENT_FINAL_REVIEW.md),
[numerator](MF-03/PADE_NUMERATOR_POLYNOMIAL_INDEPENDENT_FINAL_REVIEW.md),
[coefficient-one denominator bound](MF-03/PADE_DENOMINATOR_TAIL_INDEPENDENT_FINAL_REVIEW.md),
and [all-order high equations](MF-03/PADE_HIGH_EQUATIONS_INDEPENDENT_FINAL_REVIEW.md)
then give the frozen normalized Padé pair for every order. The
[full Target proof](MF-03/ALL_ORDER_TARGET_INDEPENDENT_FINAL_REVIEW.md)
uses the existing finite and large-order disk gates, gcd reduction, and
transport to every reduced representative.

The SP-14 partial project also contains the [independently reviewed exact
Sobolev oversampling operator algebra](SP-14/SOBOLEV_OVERSAMPLING_INDEPENDENT_FINAL_REVIEW.md):
it proves the source's displayed right inverse, range, and sharp norm estimate
from explicit two-space bounds. Its actual background-operator hypotheses
remain open.

The [finite endpoint realization's nonnegative Fourier gate](SP-14/ENDPOINT_FINITE_REALIZATION_POSITIVE_INDEPENDENT_FINAL_REVIEW.md)
now proves the exact frozen-integral Fourier coefficient of the canonical
finite product `g₀V_N` equals each physical input coefficient, including the
support tail. The [negative Fourier gate](SP-14/ENDPOINT_FINITE_REALIZATION_NEGATIVE_INDEPENDENT_FINAL_REVIEW.md)
proves every `-(t+1)` coefficient equals the physical coefficient of the
actual negative operator, with exact Sobolev weight cancellation. The
pointwise continuous-function identity remains open under the
[independently reviewed finite-realization contract](SP-14/ENDPOINT_FINITE_REALIZATION_INDEPENDENT_PRE_REVIEW.md).

The [independently reviewed physical weighted-sequence model](SP-14/WEIGHTED_SOBOLEV_PHYSICAL_INDEPENDENT_FINAL_REVIEW.md)
now identifies the complete complex `ℓ²` carrier with exactly the coefficient
sequences of finite `(n+1)^(2s)` energy and proves the exact norm-square sum.
The [independently reviewed concrete operators](SP-14/WEIGHTED_SOBOLEV_OPERATORS_INDEPENDENT_FINAL_REVIEW.md)
are continuous complex-linear inclusion, degree-`<h` truncation, and finite
lift; they preserve literal physical coefficients and prove the exact
`(q+1)^(-τ)` tail and `h^τ` finite-band inequalities. Compatible inverses and
norm bounds for the actual background operator remain open.

The [independently reviewed half-binomial base-jet inverse](SP-14/BASE_JET_BINOMIAL_INVERSE_INDEPENDENT_FINAL_REVIEW.md)
proves an exact two-sided matrix inverse and finite solve for every size,
including zero. It does not supply the actual background inverse bounds.

The [independently reviewed endpoint partial convolution](SP-14/BASE_ENDPOINT_PARTIAL_CONVOLUTION_INDEPENDENT_FINAL_REVIEW.md)
proves the exact scalar binomial identity for every finite input index and
every strictly negative output frequency. Its formal power-series proof
includes the zero input index. The actual endpoint projection matrix and
Sobolev operator estimates remain open.

The [independently reviewed actual endpoint base series and Fourier integral](SP-14/ENDPOINT_BASE_SERIES_FOURIER_INDEPENDENT_FINAL_REVIEW.md)
define `g₀(s)=Σ aₙs⁻ⁿ` on the circle, prove absolute convergence and continuity,
and compute every integer Fourier coefficient using the frozen interval integral.
The [independently reviewed finite inverse monomial and negative-frequency kernel](SP-14/ENDPOINT_EXTENSION_NEGATIVE_KERNEL_INDEPENDENT_FINAL_REVIEW.md)
now compute every negative Fourier coefficient of the actual endpoint extension
in the exact signed closed form. The [independently reviewed nonnegative
projection](SP-14/ENDPOINT_EXTENSION_POSITIVE_INDEPENDENT_FINAL_REVIEW.md)
also gives the exact Kronecker Fourier coefficients for every input and
nonnegative output index. The [independently reviewed absolute endpoint
kernel](SP-14/ENDPOINT_ABSOLUTE_KERNEL_INDEPENDENT_FINAL_REVIEW.md) identifies
the actual negative Fourier entry as
`((k+1/2)/(k+j)) Aₖ A₍ⱼ₋₁₎`, where `Aₙ=binom(2n,n)/4ⁿ>0`, and proves
`(n+1)Aₙ²≤1` and the resulting square-root entry bound for every `k≥0`,
`j≥1`. Weighted Schur sums and operator estimates remain open.

The [independently reviewed scalar Schur power comparisons](SP-14/ENDPOINT_WEIGHTED_SCHUR_POWER_INDEPENDENT_FINAL_REVIEW.md)
prove the exact finite prefix and infinite strict-tail bounds for every
`0<r<1` and `N≥1`; the strict-tail bound itself only needs `r>0`.
The [independently reviewed literal Schur row/column summands](SP-14/ENDPOINT_SCHUR_SUMS_INDEPENDENT_FINAL_REVIEW.md)
have exact global prefix/power majorants and summable row and column series
for `0<r<1` with `j≥1`, `k≥0`. The [independently reviewed scalar Schur
bounds](SP-14/ENDPOINT_SCHUR_BOUNDS_INDEPENDENT_FINAL_REVIEW.md) now prove both
uniform infinite sums at the literal `C_r=1+1/r+1/(1−r)` for all `0<r<1`,
including the endpoint indices. The [finite Schur inequalities for the actual
Fourier kernel](SP-14/ENDPOINT_WEIGHTED_KERNEL_SCHUR_INDEPENDENT_FINAL_REVIEW.md)
now hold for every cutoff, including empty sums, with this exact constant.
The [finite complex Fourier-matrix Schur bound](SP-14/ENDPOINT_FINITE_MATRIX_SCHUR_INDEPENDENT_FINAL_REVIEW.md)
now gives the exact `C_r²` squared-norm estimate for all finite input/output
cutoffs. The infinite operator estimate remains open.
The [weighted-sequence truncation density theorem](SP-14/ENDPOINT_NEGATIVE_TRUNCATION_INDEPENDENT_FINAL_REVIEW.md)
also proves that the actual first-`N` truncations tend to every input in the
literal `lp ℂ 2` carrier. The [actual negative Fourier-row bound](SP-14/ENDPOINT_NEGATIVE_ROW_INDEPENDENT_FINAL_REVIEW.md)
proves every finite row's squared norm is at most the literal `C_r²`.
The [independently reviewed row-summability gate](SP-14/ENDPOINT_NEGATIVE_ROW_SUMMABLE_INDEPENDENT_FINAL_REVIEW.md)
puts every actual row in `lp 2` and proves its product with any input is
unconditionally summable. The [actual infinite-output prefix bound](SP-14/ENDPOINT_NEGATIVE_OUTPUT_ENERGY_INDEPENDENT_FINAL_REVIEW.md)
passes the finite Fourier-matrix estimate to exact row `tsum`s and bounds
every finite output energy by `C_r²‖y‖²`. The continuous linear operator
is now [constructed from the actual Fourier entries](SP-14/ENDPOINT_NEGATIVE_OPERATOR_INDEPENDENT_FINAL_REVIEW.md)
with the literal norm bound `C_r`.
The [two-sided coefficient operator](SP-14/ENDPOINT_TWOSIDED_COEFFICIENT_INDEPENDENT_FINAL_REVIEW.md)
has the exact positive input and actual negative Fourier blocks, orthogonal
norm-square identity, and literal bound `sqrt(1+C_r²)`. Circle `H^r`
realization remains open.
The [circle coefficient summability gate](SP-14/ENDPOINT_CIRCLE_COEFF_SUMMABLE_INDEPENDENT_FINAL_REVIEW.md)
proves that every physical weighted coefficient sequence is absolutely
summable for `r>1/2`; the actual circle series remains open.
The [continuous circle series](SP-14/ENDPOINT_CIRCLE_SERIES_INDEPENDENT_FINAL_REVIEW.md)
now uses the exact positive and negative physical coefficients for `r>1/2`.
The [original-integral Fourier gate](SP-14/ENDPOINT_CIRCLE_FOURIER_INDEPENDENT_FINAL_REVIEW.md)
identifies all nonnegative and strictly negative modes of that actual
continuous circle series with the exact two-block physical coefficients.
The [conventional full-circle Sobolev energy gate](SP-14/ENDPOINT_CIRCLE_ENERGY_INDEPENDENT_FINAL_REVIEW.md)
proves summability and the exact comparison with the two-block norm, retaining
the negative-mode weight shift and factor `2^(2r)` for `1/2<r<1`.
The [explicit circle-energy bound](SP-14/ENDPOINT_CIRCLE_ENERGY_BOUND_INDEPENDENT_FINAL_REVIEW.md)
combines that comparison with the actual negative Fourier operator to give
`2^(2r)(1+C_r²)‖y‖²` with source `C_r=1+1/r+1/(1-r)`.
The [pointwise continuous Fourier uniqueness theorem](SP-14/ENDPOINT_FINITE_FOURIER_UNIQUENESS_INDEPENDENT_FINAL_REVIEW.md)
now proves that equality of every frozen normalized interval coefficient
determines a continuous circle function, through an exact AddCircle/`L²` bridge.
The [source-specific finite-input pointwise realization](SP-14/ENDPOINT_FINITE_POINTWISE_INDEPENDENT_FINAL_REVIEW.md)
now identifies the actual circle extension with `g₀V` for every finitely
supported physical input, including the endpoint zero of `g₀`.
The [exact endpoint square, zero, and truncation density gates](SP-14/ENDPOINT_VANISHING_BASICS_INDEPENDENT_FINAL_REVIEW.md)
reuse the already audited normalized series and literal `lp²` finite-coordinate
truncation.
The [actual pointwise input and difference bounds](SP-14/ENDPOINT_POINTWISE_BOUND_INDEPENDENT_FINAL_REVIEW.md)
now give that continuity with the exact `W_r(1+C_r)` factor for every circle
point. The [arbitrary-input endpoint-zero theorem](SP-14/ENDPOINT_VANISHING_BY_DENSITY_FINAL_REVIEW.md)
now passes the finite identity to every weighted input by literal truncation
density. The negative SP-14 Target remains open.
The [finite inverse Fourier gate](SP-14/ENDPOINT_FINITE_INVERSE_FOURIER_INDEPENDENT_FINAL_REVIEW.md)
identifies every actual normalized Fourier coefficient of the source's
triangular inverse polynomial, with all strictly negative modes zero.
The [Hilbert–Schmidt scalar gate](SP-14/ENDPOINT_INVERSE_HS_SCALAR_INDEPENDENT_FINAL_REVIEW.md)
now proves the exact column sum converges for every `r>1/2` and is at most
`(1+1/(r−1/2))²`.
The [finite inverse coefficient-energy gate](SP-14/ENDPOINT_FINITE_INVERSE_ENERGY_INDEPENDENT_FINAL_REVIEW.md)
now bounds the actual triangular inverse's first `N` coefficient squares by
the exact Hilbert–Schmidt sum times the literal weighted input norm squared,
including `N=0`.
The [finite inverse Parseval gate](SP-14/ENDPOINT_FINITE_INVERSE_PARSEVAL_INDEPENDENT_FINAL_REVIEW.md)
now identifies the exact normalized real-interval square integral and the
probability-Haar `Lp` norm square with the actual first `N` triangular inverse
coefficient energy. The finite operator bound and infinite inverse extension
remain open.

The following RA-10 paragraphs record incremental proof gates as they were
completed. Any intermediate "remaining" steps described there are historical;
the full pinned target is now verified as recorded in the full-target table.

The [RA-10 selected-projector gates](RA-10/SELECTED_PROJECTOR_INDEPENDENT_FINAL_REVIEW.md)
identify the exact frozen first-`k` eigenvector projector, prove symmetry and
idempotence from every supplied ordered decomposition, and give rank `k` for
`k≤n`, including tied and zero eigenvalues. The [supported functional-calculus identity](RA-10/SELECTED_PROJECTION_FUNCTION_INDEPENDENT_FINAL_REVIEW.md)
holds for every real `f`, including `f(0)>0`, with the same supplied `Q`.
The pinching contraction is proved by the audited later gate below.
The [independently reviewed shifted-inverse gate](RA-10/RIDGE_SHIFT_INVERSE_INDEPENDENT_FINAL_REVIEW.md)
identifies the exact frozen reciprocal spectral matrix with the actual
inverse of `sI+A` for every supplied PSD decomposition and `s>0`.
The [ridge-resolvent matrix gate](RA-10/RIDGE_RESOLVENT_MATRIX_INDEPENDENT_FINAL_REVIEW.md)
proves the exact frozen ridge functional calculus and the source-oriented
`f_s(C)−f_s(A)` subtraction with literal factor `s`.
The [noncommutative resolvent product gate](RA-10/RIDGE_RESOLVENT_PRODUCT_INDEPENDENT_FINAL_REVIEW.md)
establishes shifted invertibility and both exact product orders for that
difference, including the source's Equation (14) order.
The [matched-leading ridge gate](RA-10/MATCHED_LEADING_RIDGE_INDEPENDENT_FINAL_REVIEW.md)
constructs `B₀` in the supplied selected basis and proves the exact matrix
equality underlying Equation (14).
The [basic Loewner factor gate](RA-10/RIDGE_RESOLVENT_LOEWNER_BASIC_INDEPENDENT_FINAL_REVIEW.md)
proves `0≼(sI+A)⁻¹≼(1/s)I` and the exact zero-based cutoff witness.
The [sharp selected Loewner gate](RA-10/RIDGE_RESOLVENT_LOEWNER_SELECTED_INDEPENDENT_FINAL_REVIEW.md)
proves `0≼P(sI+B₀)⁻¹P≼[1/(s+c)]P` with source `c=a_k` and the same
supplied selected eigenbasis.
The [first Euclidean operator-norm factor](RA-10/RIDGE_RESOLVENT_OPNORM_BASIC_INDEPENDENT_FINAL_REVIEW.md)
proves the actual full shifted inverse has L2 operator norm at most `1/s`.
The [selected Euclidean operator-norm factor](RA-10/RIDGE_RESOLVENT_OPNORM_SELECTED_INDEPENDENT_FINAL_REVIEW.md)
proves the actual `P(sI+B₀)⁻¹P` has L2 operator norm at most the sharp
`1/(s+c)` with source `c=a_k`.
The [matched-leading support algebra](RA-10/MATCHED_LEADING_SUPPORT_INDEPENDENT_FINAL_REVIEW.md)
proves `P(B₀−PAP)P=B₀−PAP` and inserts the same `P` around the left inverse in
the exact noncommutative Equation (14) product.
The [actual-compression Equation (14) gate](RA-10/MATCHED_LEADING_EQ14_RESTRICTED_INDEPENDENT_FINAL_REVIEW.md)
retains `C=PAP`, source factor `s`, matrix order, and literal frozen nuclear-norm
equality under a supplied decomposition of that `C`.
The [selected-compression PSD gate](RA-10/SELECTED_COMPRESSION_PSD_INDEPENDENT_FINAL_REVIEW.md)
proves the exact quadratic identity and both frozen PSD conjuncts for actual
`C=PAP`; constructing its sorted spectral decomposition remains open.
The [frozen-to-Mathlib PSD bridge](RA-10/CUSTOM_PSD_MATHLIB_BRIDGE_INDEPENDENT_FINAL_REVIEW.md)
proves an exact iff in every finite real dimension and applies it to the same
actual `C=PAP`. The [ordered spectral construction](RA-10/SELECTED_COMPRESSION_ORDERED_SPECTRAL_INDEPENDENT_FINAL_REVIEW.md)
constructs all four frozen spectral conjuncts for this actual compression;
the [positive-eigenvector support lemma](RA-10/SELECTED_COMPRESSION_POSITIVE_EIGENVECTOR_INDEPENDENT_FINAL_REVIEW.md)
shows each positive C eigenvector lies in the original selected range. The
[constructed-witness Equation (14)](RA-10/MATCHED_LEADING_EQ14_CONSTRUCTED_INDEPENDENT_FINAL_REVIEW.md)
discharges the separate hC premise for the exact matrix and nuclear norm
equalities. The compression eigenvalue comparison remains open under its
[reviewed min-max contract](RA-10/SELECTED_COMPRESSION_EIGENVALUE_INDEPENDENT_PRE_REVIEW.md),
with [exact Rayleigh dependencies](RA-10/ORDERED_SPECTRAL_RAYLEIGH_INDEPENDENT_PRE_REVIEW.md)
now [kernel proved](RA-10/ORDERED_SPECTRAL_RAYLEIGH_INDEPENDENT_FINAL_REVIEW.md).
The simultaneous nonzero coordinate intersection has its
[independently reviewed proof](RA-10/ORDERED_SPECTRAL_INTERSECTION_INDEPENDENT_FINAL_REVIEW.md).
The actual positive-prefix support step has an
[independently reviewed proof](RA-10/SELECTED_COMPRESSION_PREFIX_SUPPORT_INDEPENDENT_FINAL_REVIEW.md).
The [exact compression comparison](RA-10/SELECTED_COMPRESSION_COMPARISON_INDEPENDENT_FINAL_REVIEW.md)
now proves the source coefficient-one `0≤h_i≤a_i` for the actual selected
`C=PAP` and every supplied ordered decomposition, including ties and zeros.
The [exact matrix/operator bridge](RA-10/NUCLEAR_IDEAL_OPERATOR_BRIDGE_INDEPENDENT_FINAL_REVIEW.md)
identifies the frozen `Fin n` singular-value sum after matrix composition
and the scoped L2 matrix norm with its Euclidean operator norm.
[Homogeneity](RA-10/NUCLEAR_NORM_HOMOGENEITY_INDEPENDENT_FINAL_REVIEW.md),
[left invariance](RA-10/NUCLEAR_ORTHOGONAL_LEFT_INDEPENDENT_FINAL_REVIEW.md),
[right invariance](RA-10/NUCLEAR_ORTHOGONAL_RIGHT_INDEPENDENT_FINAL_REVIEW.md),
and [two-sided invariance](RA-10/NUCLEAR_ORTHOGONAL_CONJUGATION_INDEPENDENT_FINAL_REVIEW.md)
of that exact nuclear norm are kernel proved. The
[same-index PSD Loewner eigenvalue bound](RA-10/ORDERED_PSD_LOEWNER_EIGENVALUE_INDEPENDENT_FINAL_REVIEW.md)
and [sharp left Gram order](RA-10/NUCLEAR_IDEAL_GRAM_ORDER_INDEPENDENT_FINAL_REVIEW.md)
are also kernel proved. The [exact same-index Gram eigenvalue/singular-value
square bridge](RA-10/NUCLEAR_IDEAL_GRAM_INDEX_INDEPENDENT_FINAL_REVIEW.md)
now covers every supplied ordered Gram decomposition. The
[coefficient-one same-index left singular-value bound](RA-10/NUCLEAR_IDEAL_POINTWISE_LEFT_INDEPENDENT_FINAL_REVIEW.md)
is kernel proved for every `Fin n` index. Its sum gives the
[exact frozen nuclear-norm left ideal inequality](RA-10/NUCLEAR_IDEAL_LEFT_INDEPENDENT_FINAL_REVIEW.md).
The [same-index transpose singular values](RA-10/NUCLEAR_SINGULAR_VALUES_TRANSPOSE_INDEPENDENT_FINAL_REVIEW.md),
[frozen nuclear-norm transpose](RA-10/NUCLEAR_NORM_TRANSPOSE_INDEPENDENT_FINAL_REVIEW.md),
and [scoped L2 operator-norm transpose](RA-10/NUCLEAR_OPERATOR_NORM_TRANSPOSE_INDEPENDENT_FINAL_REVIEW.md)
then give the [coefficient-one right ideal inequality](RA-10/NUCLEAR_IDEAL_RIGHT_INDEPENDENT_FINAL_REVIEW.md).
The [sharp selected resolvent nuclear product](RA-10/NUCLEAR_IDEAL_EQ14_PRODUCT_INDEPENDENT_FINAL_REVIEW.md)
and [restricted ridge difference inequality](RA-10/NUCLEAR_IDEAL_EQ14_RESTRICTED_INDEPENDENT_FINAL_REVIEW.md)
now prove the source's exact Equation (14) with coefficient `1/(s+a_k)`.
The [orthogonal trace upper bound](RA-10/NUCLEAR_TRACE_DUAL_UPPER_INDEPENDENT_FINAL_REVIEW.md)
uses the actual Gram eigenbasis to prove `trace(UᵀM)≤NuclearNorm M` at
coefficient one for arbitrary `M` and orthogonal `U` in every dimension.
The [attainment theorem](RA-10/NUCLEAR_TRACE_DUAL_ATTAINS_INDEPENDENT_FINAL_REVIEW.md)
constructs a matching orthogonal `U` for every `M`, including rank-deficient and
zero matrices, with equality at the full frozen singular-value sum.
The [sharp triangle inequality](RA-10/NUCLEAR_NORM_TRIANGLE_INDEPENDENT_FINAL_REVIEW.md)
then follows by applying that maximizer to a sum and using the upper bound on
each summand. The [pinching contraction](RA-10/NUCLEAR_PINCHING_INDEPENDENT_FINAL_REVIEW.md)
then follows at coefficient one from the reflection average, homogeneity,
triangle, and orthogonal invariance, under the
[independently approved exact duality contract](RA-10/NUCLEAR_PINCHING_DUAL_INDEPENDENT_PRE_REVIEW.md).
The [PSD nuclear-trace identity](RA-10/NUCLEAR_NORM_PSD_TRACE_INDEPENDENT_FINAL_REVIEW.md)
now supplies the exact positive-block accounting for source Equation (8).
The [complementary-block additivity theorem](RA-10/NUCLEAR_COMPLEMENTARY_BLOCKS_INDEPENDENT_FINAL_REVIEW.md)
now gives the exact coefficient-one identity for every pair of blocks supported
on a symmetric projection and its complement. The [source Equation (8)
calculation](RA-10/MATCHED_LEADING_EQ8_INDEPENDENT_FINAL_REVIEW.md) now proves
the exact selected-compression excess and trace-loss inequality with both
supplied bases and the original tail. [Source Equation (9)](RA-10/MATCHED_LEADING_EQ9_TRIANGLE_INDEPENDENT_FINAL_REVIEW.md)
then gives the exact coefficient-one compression-excess triangle with that same
tail. [Equation (10)](RA-10/MATCHED_LEADING_EQ10_POSITIVE_PART_INDEPENDENT_PRE_REVIEW.md)
has an independently approved positive-part contract. Its [generic frozen-norm
identity](RA-10/HERMITIAN_POSITIVE_PART_INDEPENDENT_FINAL_REVIEW.md) is now
kernel proved for every real Hermitian matrix; the [source compression
Equation (10)](RA-10/MATCHED_LEADING_EQ10_POSITIVE_PART_INDEPENDENT_FINAL_REVIEW.md)
is now assembled with both supplied bases and the original trace tail.
The exact [Equation (11) defect contract](RA-10/MATCHED_LEADING_EQ11_DEFECT_INDEPENDENT_PRE_REVIEW.md)
is approved for staged implementation. Its [arbitrary selected-compression
eigenvalue-tail and trace-prefix gates](RA-10/SELECTED_COMPRESSION_TAIL_INDEPENDENT_FINAL_REVIEW.md)
now prove every supplied compression spectrum has zero tail from index `k`,
including repeated and zero eigenvalues. The [scalar deficit sum](RA-10/MATCHED_LEADING_EQ11_SCALAR_INDEPENDENT_FINAL_REVIEW.md)
is now bounded by `L` at coefficient one. The [independently reviewed
variational bridge](RA-10/MATCHED_LEADING_EQ11_VARIATIONAL_INDEPENDENT_FINAL_REVIEW.md)
proves the actual matrix positive-part trace is at most that scalar sum,
then at most `L`, including rank-deficient compressions and arbitrary supplied
compression eigenbases. The restricted-block trace notation used for source
`d` still needs an explicit formal bridge during later integration.
The [positive-cutoff ridge trace-loss theorem](RA-10/MATCHED_LEADING_EQ12_RIDGE_LOSS_INDEPENDENT_FINAL_REVIEW.md)
now proves exact `0≤L_s≤L/(s+c)` with the actual full-space functional
matrix and zero compression tail. The [first Equation (13) trace
identity](RA-10/MATCHED_LEADING_EQ13_TRACE_IDENTITY_INDEPENDENT_FINAL_REVIEW.md)
now equates the exact ridge nuclear excess with `L_s` plus twice the
positive-part trace of `F_C−F_A`. Subsequent proof development discharged the
`c=0` branch, Lemma 2's positive-part bound, Equation (13), compression,
perturbation, integral transfer, and the full Target. The
[final source reviews](../../../randomized-and-low-rank-approximation/RA-10/lean/reviews/FINAL_FORMALIZATION_REVIEW_1.md)
and [isolated kernel receipt](RA-10/LINUX_CI_RECEIPT.md) cover the pinned full proof.

The [independently reviewed normalized exterior boundary factor](SP-14/BASE_EXTERIOR_FACTOR_INDEPENDENT_FINAL_REVIEW.md)
is a continuous half-binomial series with exact square, endpoint zero, and
base-symbol factor identities. Exterior holomorphy and finite-background
smallness estimates remain open.

The [independently reviewed finite real Laurent background](SP-14/FINITE_LAURENT_BACKGROUND_INDEPENDENT_FINAL_REVIEW.md)
has exact strict-sign corrections, continuous source boundary objects,
`h−s=2s g₀P+sP²`, the corrected symbol identity, and separate contact at
`−1`, including empty and nonempty endpoint cases. Analytic estimates remain
open.

The [independently reviewed finite negative Laurent endpoint division](SP-14/NEGATIVE_LAURENT_ENDPOINT_DIVISION_INDEPENDENT_FINAL_REVIEW.md)
derives `P₋=(1+s)Q₋` from the actual separate contact equation for every
finite coefficient length, including zero and one. Weighted convolution and
background estimates remain open.

The [independently reviewed negative-product Fourier support](SP-14/NEGATIVE_PRODUCT_FOURIER_SUPPORT_INDEPENDENT_FINAL_REVIEW.md)
proves the actual `g₀P₋` has zero frozen Fourier coefficient at every
nonnegative frequency under the same contact premise. Its
[literal weighted norm bound](SP-14/ACTUAL_NEGATIVE_WIENER_BOUND_INDEPENDENT_FINAL_REVIEW.md)
is also proved from the actual contact-derived quotient. The remaining
estimates are open.

The [independently reviewed regularized exterior coefficients](SP-14/REGULARIZED_BASE_COEFF_INDEPENDENT_FINAL_REVIEW.md)
satisfy the exact endpoint-cancellation recurrence and unconditional
`9/8`-weighted summability. The [independently reviewed actual regularized
factor](SP-14/REGULARIZED_FACTOR_FOURIER_INDEPENDENT_FINAL_REVIEW.md) has an
exact circle series and all-integer Fourier coefficients under the frozen
integral. Its [literal bilateral weighted Wiener size](SP-14/REGULARIZED_FACTOR_WIENER_INDEPENDENT_FINAL_REVIEW.md)
is finite with the exact positive singleton and regularized negative tail.
The [finite negative Laurent correction](SP-14/FINITE_NEGATIVE_WIENER_INDEPENDENT_FINAL_REVIEW.md)
also has a literal Wiener size equal to its finite coefficient sum.
The [generic finite negative Laurent multiplier](SP-14/FINITE_NEGATIVE_WIENER_MULTIPLIER_INDEPENDENT_FINAL_REVIEW.md)
preserves literal weighted Fourier summability and satisfies the
constant-one weighted Wiener product bound.
The [canonical first Wiener sizes](SP-14/CANONICAL_FIRST_WIENER_SIZES_INDEPENDENT_FINAL_REVIEW.md)
give exact finite negative W⁰ and positive W⁴ norms under the frozen
Fourier integral and prove the exterior base factor's W⁰ size is at most two.
The [positive endpoint and continuous negative ratio](SP-14/POSITIVE_ENDPOINT_RATIO_INDEPENDENT_FINAL_REVIEW.md)
also have exact finite factorization and off-endpoint quotient identity.
The [actual ratio extension's W⁰ size](SP-14/NEGATIVE_RATIO_W0_INDEPENDENT_FINAL_REVIEW.md)
is summable with the constant-one bound by `W⁰(g₀)Σ|qⱼ|`.
The [finite positive Laurent multiplier](SP-14/FINITE_POSITIVE_WIENER_MULTIPLIER_INDEPENDENT_FINAL_REVIEW.md)
has exact frequency shifts and a constant-one `W^(9/8)` product bound.
The [actual positive Laurent literal weighted size](SP-14/FINITE_POSITIVE_WIENER_SIZE_INDEPENDENT_FINAL_REVIEW.md)
equals its exact finite coefficient sum.
The [literal weighted Wiener addition inequality](SP-14/WIENER_ADD_INDEPENDENT_FINAL_REVIEW.md)
also holds with constant one for continuous weighted-summable functions.
The [actual finite correction and its square](SP-14/FINITE_CORRECTION_SQUARE_WIENER_INDEPENDENT_FINAL_REVIEW.md)
have summable weighted coefficients and the constant-one square bound.
The [circle-mode shift](SP-14/WIENER_SHIFT_INDEPENDENT_FINAL_REVIEW.md)
costs exactly the `2^(9/8)` weight in the norm bound.
The [actual finite-background deviation](SP-14/FINITE_BACKGROUND_DEVIATION_WIENER_INDEPENDENT_FINAL_REVIEW.md)
now has the reviewed literal `W^(9/8)` bound for all finite corrections
with separate endpoint contact.
The [strict two-mode first-smallness witness](SP-14/TWO_MODE_FIRST_SMALLNESS_INDEPENDENT_FINAL_REVIEW.md)
now supplies a nonzero finite background satisfying all five literal
source inequalities for any positive threshold. Stagewise packet control,
the compatible inverse, and the infinite limit remain open.

The TR-14 chart work also has an [independently reviewed complete coefficient
basis](TR-14/GL2_COEFFICIENT_BASIS_INDEPENDENT_FINAL_REVIEW.md) for genuine
homogeneous binary forms, including the exact monomial product index. The
[unweighted homogeneous moment dual and its inverse-dual chart relation](TR-14/GL2_MOMENT_DUAL_INDEPENDENT_FINAL_REVIEW.md)
and [all-degree apolar product equivalence](TR-14/GL2_APOLAR_PAIRING_INDEPENDENT_FINAL_REVIEW.md)
are also kernel checked. The [inverse-dual chart transport of every apolar
kernel and nonzero apolar degree](TR-14/GL2_APOLAR_TRANSPORT_INDEPENDENT_FINAL_REVIEW.md)
is kernel checked as well. The ordinary-to-symmetric rank comparison remains
a separate proof obligation.

The [independently reviewed affine dehomogenization and chart-selection
lemma](TR-14/GL2_DEHOMOGENIZE_INDEPENDENT_FINAL_REVIEW.md) recovers every
coefficient, proves the transformed final coefficient equals exact polynomial
evaluation, and selects a chart where it is nonzero for any chosen nonzero
form. This supplies the chart used by the monic normalization below.
The [full affine chart polynomial identity](TR-14/GL2_AFFINE_CHART_POLYNOMIAL_INDEPENDENT_FINAL_REVIEW.md)
now gives every coefficient of the transported degree-`d` form as
`G(t,1+zt)=Σᵢ gᵢ t^(d−i)(1+zt)^i`, including trailing zeros and infinity
cases. The projective-root multiplicity correspondence remains open.
The [nonzero affine-coordinate identity](TR-14/GL2_MOBIUS_EVAL_INDEPENDENT_FINAL_REVIEW.md)
now gives the exact degree-`d` Möbius evaluation `p_z(t)=t^d p(z+t⁻¹)`
for every `t≠0`, including trailing-zero forms. Root multiplicity and the
exceptional zero coordinate remain open.
The [nonzero finite-root equivalence](TR-14/GL2_NONZERO_ROOT_CORRESPONDENCE_INDEPENDENT_FINAL_REVIEW.md)
now proves both exact inverse coordinate maps between original roots away
from `z` and transformed roots away from zero. Multiplicity and projective
infinity cases remain open.

The [independently reviewed chosen least-apolar normalization](TR-14/GL2_CHART_NORMALIZE_INDEPENDENT_FINAL_REVIEW.md)
now transports any supplied nonzero least witness to a monic affine polynomial
of exact degree and preserves nonzero moments and every lower zero apolar
kernel. All-width tensor equality remains open.

The [independently reviewed exact Hankel mode pairing](TR-14/GL2_HANKEL_MODE_INDEPENDENT_FINAL_REVIEW.md)
expands the tensor contraction with no multinomial factors and proves the
inverse-dual chart identity on every mode vector. Frozen ordinary/symmetric
width equivalences follow in the [independently reviewed width transport](TR-14/GL2_WIDTH_TRANSPORT_INDEPENDENT_FINAL_REVIEW.md)
for every width including zero. The [middle-rank transport and original-coordinate
least-apolar rank theorem](TR-14/GL2_MIDDLE_RANK_TRANSPORT_INDEPENDENT_FINAL_REVIEW.md)
are also kernel checked. The two symmetric upper constructions and general
ordinary-rank lower bound remain separate obligations.

The [independently reviewed local Fourier filter](TR-14/LOCAL_FOURIER_FILTER_INDEPENDENT_FINAL_REVIEW.md)
recovers one local top coefficient with exactly `(m−1)(ℓ−1)+1` root-of-unity
nodes for every `m≥3`, `ℓ≥1`, including `ℓ=1`. Global node reindexing
and the symmetric tensor upper bound remain to be proved.

The [independently reviewed moment-to-quotient mode pairing](TR-14/MOMENT_QUOTIENT_MODE_PAIRING_INDEPENDENT_FINAL_REVIEW.md)
identifies each genuine affine mode polynomial with its quotient image and
proves the exact all-moment Hankel product identity, including empty modes and
top degree. Local-functional reconstruction and width conclusions remain open.

The [independently reviewed local top-coefficient algebra](TR-14/LOCAL_TOP_COEFFICIENT_INDEPENDENT_FINAL_REVIEW.md)
proves the exact truncated power basis, coefficient convolution, and unique
reversed-coefficient representation of every local linear functional. Its
Frobenius nonzero and finite-root consequences are now proved in the
[independently reviewed local unit/root module](TR-14/LOCAL_UNIT_ROOT_INDEPENDENT_FINAL_REVIEW.md).
The [independently reviewed one-factor Fourier decomposition](TR-14/LOCAL_ONE_FACTOR_FOURIER_INDEPENDENT_FINAL_REVIEW.md)
expresses every genuine local Frobenius product as exactly
`(m−1)(ℓ−1)+1` same-factor terms. Its [exact zero-based mode-vector
corollary](TR-14/LOCAL_FOURIER_MODE_INDEPENDENT_FINAL_REVIEW.md) supplies
the corresponding local tensor-coordinate vectors for arbitrary `ℓ>0`.
Global node reindexing and width conclusions remain open.
The [independently reviewed root-data gate](TR-14/LOCAL_CRT_ROOT_DATA_INDEPENDENT_FINAL_REVIEW.md)
retains every multiplicity and proves the exact monic factorization,
degree sum, and pairwise coprimality of the root-factor powers.
The [independently reviewed primary shift](TR-14/LOCAL_CRT_SHIFT_INDEPENDENT_FINAL_REVIEW.md)
is a genuine complex-algebra equivalence for each one-root power quotient
and carries its quotient root exactly to the root scalar plus local nilpotent
generator. The [full algebra CRT equivalence](TR-14/LOCAL_CRT_ALGEBRA_INDEPENDENT_FINAL_REVIEW.md)
now identifies the monic quotient with the product of all such local
algebras and gives the exact quotient-root image, powers, and finite
products. The [supported local-functional transfer](TR-14/LOCAL_CRT_FUNCTIONAL_INDEPENDENT_FINAL_REVIEW.md)
decomposes every quotient functional and derives local Frobenius
nondegeneracy from global Frobenius. The all-moment Hankel reconstruction
is now proved from actual monic apolarity in the [independently reviewed
moment transfer](TR-14/LOCAL_CRT_MOMENTS_INDEPENDENT_FINAL_REVIEW.md),
including every supplied moment and zero-based tensor coordinate. The
global width theorem remains open.
The [independently reviewed dependent root/Fourier sum](TR-14/LOCAL_CRT_FOURIER_SIGMA_INDEPENDENT_FINAL_REVIEW.md)
now gives every frozen Hankel coordinate as a finite sum of same-vector
symmetric terms under actual nonzero least-apolar hypotheses. Its
[independently reviewed exact node count and frozen symmetric width construction](TR-14/LOCAL_CRT_FOURIER_WIDTH_INDEPENDENT_FINAL_REVIEW.md)
give one normalized-chart upper bound, including repeated roots. The
original-coordinate projective root count, other width bounds, and full Target remain open.

## Shared statement only; no live proof source (29)

The following files define a `Target : Prop` and pass statement-boundary checks.
They have no full live proof. The source-path pattern is
`lean-statements/NLA/Statements/IDWITHOUTDASH.lean`.

| ID | Statement source | ID | Statement source |
| --- | --- | --- | --- |
| AA-01 | [`AA01.lean`](../../../lean-statements/NLA/Statements/AA01.lean) | AV-01 | [`AV01.lean`](../../../lean-statements/NLA/Statements/AV01.lean) |
| AV-02 | [`AV02.lean`](../../../lean-statements/NLA/Statements/AV02.lean) | FR-10 | [`FR10.lean`](../../../lean-statements/NLA/Statements/FR10.lean) |
| IE-08 | [`IE08.lean`](../../../lean-statements/NLA/Statements/IE08.lean) | IE-10 | [`IE10.lean`](../../../lean-statements/NLA/Statements/IE10.lean) |
| IE-12 | [`IE12.lean`](../../../lean-statements/NLA/Statements/IE12.lean) | IE-26 | [`IE26.lean`](../../../lean-statements/NLA/Statements/IE26.lean) |
| IV-05 | [`IV05.lean`](../../../lean-statements/NLA/Statements/IV05.lean) | MF-08 | [`MF08.lean`](../../../lean-statements/NLA/Statements/MF08.lean) |
| MI-16 | [`MI16.lean`](../../../lean-statements/NLA/Statements/MI16.lean) | MI-31 | [`MI31.lean`](../../../lean-statements/NLA/Statements/MI31.lean) |
| NM-03 | [`NM03.lean`](../../../lean-statements/NLA/Statements/NM03.lean) | PF-04 | [`PF04.lean`](../../../lean-statements/NLA/Statements/PF04.lean) |
| PF-05 | [`PF05.lean`](../../../lean-statements/NLA/Statements/PF05.lean) | RA-04 | [`RA04.lean`](../../../lean-statements/NLA/Statements/RA04.lean) |
| RA-05 | [`RA05.lean`](../../../lean-statements/NLA/Statements/RA05.lean) | RA-12 | [`RA12.lean`](../../../lean-statements/NLA/Statements/RA12.lean) |
| RA-13 | [`RA13.lean`](../../../lean-statements/NLA/Statements/RA13.lean) | RA-19 | [`RA19.lean`](../../../lean-statements/NLA/Statements/RA19.lean) |
| RE-05 | [`RE05.lean`](../../../lean-statements/NLA/Statements/RE05.lean) | RE-06 | [`RE06.lean`](../../../lean-statements/NLA/Statements/RE06.lean) |
| SP-13 | [`SP13.lean`](../../../lean-statements/NLA/Statements/SP13.lean) | | |
| TR-06 | [`TR06.lean`](../../../lean-statements/NLA/Statements/TR06.lean) | TR-08 | [`TR08.lean`](../../../lean-statements/NLA/Statements/TR08.lean) |
| TR-17 | [`TR17.lean`](../../../lean-statements/NLA/Statements/TR17.lean) | TR-20 | [`TR20.lean`](../../../lean-statements/NLA/Statements/TR20.lean) |
| TR-21 | [`TR21.lean`](../../../lean-statements/NLA/Statements/TR21.lean) | TR-26 | [`TR26.lean`](../../../lean-statements/NLA/Statements/TR26.lean) |

LeanCert `#assert_statement`, `#assert_trust kernel`, frozen identity checks,
and the shared Comparator certificates check statement definitions and their
trust closure. They do not prove any of the 29 statement-only propositions or
upgrade the eight partial projects to full proofs. Complete-target wrappers
still require their own reviewed exact-revision verification and promotion.
