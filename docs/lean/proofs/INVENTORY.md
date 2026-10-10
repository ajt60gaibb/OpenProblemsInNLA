# Proof inventory for the 47 Solved problems

This is a source-level inventory against `problem_ids.json` and the canonical
README status fields at the current branch. It records proof availability, not
mathematical correctness or a `Lean verified` status. Permanent IDs and
canonical READMEs are unchanged. Historical copies under `reviews/`,
`verification/`, and archive directories are evidence, not live solution
sources.

## Full-target local proof candidates (4)

| ID | Live proof source | Evidence and remaining gate |
| --- | --- | --- |
| FR-05 | [`Solution.lean`](../../../frames-and-matrix-designs/FR-05/lean/Solution.lean) | Exports the original Gaussian/all-signals limit and the stronger `C/d` bound. Independent [source review](FR-05/INDEPENDENT_REVIEW.md) and the [isolated Linux Comparator/LeanCert kernel receipt](FR-05/LINUX_CI_RECEIPT.md) pass with only standard axioms. The separate `Challenge.lean` contains deliberate `sorry`s and is not imported by `Solution`. |
| TR-13 | [`Solution.lean`](../../../tensor-computations/TR-13/lean/Solution.lean) | Exports `NLA.TR13.generic_rank_equality` and the [independently reviewed all-width bridge](TR-13/EXACT_STATEMENT_INDEPENDENT_REVIEW.md) for every odd `m ≥ 5`, `n ≥ 2`, with all five exact generic ranks and equivalence at every natural width. The [isolated Linux Comparator/LeanCert kernel receipt](TR-13/LINUX_CI_RECEIPT.md) passes with only standard axioms. |
| MF-23 | [`CanonicalBridge.lean`](../../../matrix-functions-and-stability/MF-23/lean/CanonicalBridge.lean) | Proves the [reviewed canonical block-order target](MF-23/CANONICAL_BRIDGE_INDEPENDENT_REVIEW.md) from the pinned external `complete_crouzeix` proof by a norm-preserving tensor-factor swap. Its self-contained source-locked project and [isolated Linux Comparator/LeanCert kernel receipt](MF-23/LINUX_CI_RECEIPT.md) pass with only standard axioms. |
| RA-06 | [`Final.lean`](../../../lean-statements/NLA/Proofs/RA06/Final.lean) | The [independently reviewed full theorem](RA-06/FINAL_INDEPENDENT_REVIEW.md) inhabits the frozen original negative `Target` for every `p > 2`, with the exact sampler, same `α`, expected retained count, and raw log budget. The [isolated Linux Comparator/LeanCert kernel receipt](RA-06/LINUX_CI_RECEIPT.md) passes with only standard axioms. |

## Local partial solution projects (9)

| ID | Live source | What is actually proved |
| --- | --- | --- |
| IE-21 | [`Solution.lean`](../../../linear-systems-and-elimination/IE-21/lean/Solution.lean) | Zero vector and empty row-energy lemmas. The full target is an axiom and the spherical-row law semantics remain unimplemented. |
| IE-22 | [`Solution.lean`](../../../linear-systems-and-elimination/IE-22/lean/Solution.lean) | Zero vector and empty row-energy lemmas. The full target is an axiom; complete semantics and proof remain. |
| IV-02 | [`Solution.lean`](../../../intervals-and-absolute-value-equations/IV-02/lean/Solution.lean) | Rotation identity and positive even layer count. The original complexity claim remains absent from the implemented semantics. |
| IV-04 | [`Solution.lean`](../../../intervals-and-absolute-value-equations/IV-04/lean/Solution.lean) | A two-by-two corner algebra lemma. The original complexity target is absent and the current statement's interval semantics have a known scope gap. |
| MD-06 | [`Solution.lean`](../../../matrix-discrepancy-and-optimization/MD-06/lean/Solution.lean) | Extracts a nonsynchronized critical point from an assumed stable event. Graph probability and local-minimum semantics are parameters of an abstract structure. |
| MF-03 | [`FiniteRange.lean`](../../../lean-statements/NLA/Proofs/MF03/FiniteRange.lean) | Proves the exact frozen target clause for every order 1–15, including reduced-pair existence and every reduced representative, from [independently reviewed](MF-03/FINITE03_15_INDEPENDENT_REVIEW.md) exact certificates, gcd reduction and disk transport. Separate [all-order cosine-tail](MF-03/COSINE_TAIL_INDEPENDENT_FINAL_REVIEW.md), [value-at-three/numeric-margin](MF-03/WAVE_AT_THREE_INDEPENDENT_FINAL_REVIEW.md), and [complex factor-product convergence](MF-03/COSINE_PRODUCT_INDEPENDENT_PARTIAL_REVIEW.md) lemmas are kernel checked. The [conditional large-order disk theorem](MF-03/LARGE_ORDER_DISK_INDEPENDENT_FINAL_REVIEW.md) is kernel checked for any normalized pair satisfying the source's denominator coefficient bounds. The product value identity and exact elementary-symmetric coefficient transfer are kernel checked; [finite-tableau restriction and the exact bottom-label bound](MF-03/FINITE_TABLEAU_BOTTOM_INDEPENDENT_FINAL_REVIEW.md), [injective restriction-plus-bottom-tuple map](MF-03/FINITE_TABLEAU_PAIR_INDEPENDENT_FINAL_REVIEW.md), [exact weight factorization](MF-03/FINITE_TABLEAU_WEIGHT_FACTOR_INDEPENDENT_FINAL_REVIEW.md), [the finite weighted-tableau tail inequality](MF-03/FINITE_TABLEAU_TAIL_BOUND_INDEPENDENT_FINAL_REVIEW.md), [strict positivity of the finite rectangle and augmented tableau sums](MF-03/FINITE_TABLEAU_CANONICAL_INDEPENDENT_FINAL_REVIEW.md), [comparison with the exact infinite cosine tail](MF-03/FINITE_TABLEAU_INFINITE_TAIL_INDEPENDENT_FINAL_REVIEW.md), [the exact finite elementary coefficients' monotone limit to the original infinite coefficients](MF-03/FINITE_ELEMENTARY_LIMIT_INDEPENDENT_FINAL_REVIEW.md), and [fixed-size rectangular/augmented determinant limits](MF-03/FINITE_DETERMINANT_LIMIT_INDEPENDENT_FINAL_REVIEW.md) are now also checked. Determinant/tableau identities, all-order pair existence and denominator bounds, orders ≥16, and the full all-order target remain unproved. |
| SP-14 | [`SubsequenceGap.lean`](../../../lean-statements/NLA/Proofs/SP14/SubsequenceGap.lean) | [Independently reviewed](SP-14/SUBSEQUENCE_GAP_INDEPENDENT_FINAL_REVIEW.md) kernel proof that a supplied continuous counterexample with a positive eventual empirical gap refutes the exact frozen conjecture. Separate [base-coefficient convolution](SP-14/BASE_COEFFICIENT_INDEPENDENT_REVIEW.md), [unconditional coefficient-defined block product](SP-14/BASE_CB_INDEPENDENT_FINAL_REVIEW.md), [frozen-integral monomial Fourier orthogonality](SP-14/BASE_FOURIER_MODE_INDEPENDENT_REVIEW.md), [absolute summability of the exterior half-binomial coefficients](SP-14/BASE_COEFF_SUMMABLE_INDEPENDENT_REVIEW.md), [continuous exterior boundary series](SP-14/BASE_EXTERIOR_SERIES_INDEPENDENT_REVIEW.md), [termwise frozen Fourier integration](SP-14/BASE_EXTERIOR_FOURIER_INDEPENDENT_REVIEW.md), [the exterior base symbol's exact Fourier pattern and actual odd Toeplitz characteristic polynomial](SP-14/BASE_EXTERIOR_PATTERN_INDEPENDENT_REVIEW.md), [its boundary square and zero identities](SP-14/BASE_EXTERIOR_BOUNDARY_SQUARE_INDEPENDENT_REVIEW.md), [positive packet Fourier support and small-section invisibility](SP-14/POSITIVE_PACKET_INVISIBILITY_INDEPENDENT_FINAL_REVIEW.md), [finite negative-restoration algebra and earlier-section persistence](SP-14/NEGATIVE_RESTORATION_INVISIBILITY_INDEPENDENT_FINAL_REVIEW.md), [the conditional all-order odd-frequency Toeplitz characteristic polynomial in the jet coordinate](SP-14/ODD_FREQUENCY_TOEPLITZ_CHARPOLY_INDEPENDENT_FINAL_REVIEW.md), [continuous odd Fourier support and jet polynomial shape for every finite corrected symbol](SP-14/FINITE_CORRECTED_ODD_SUPPORT_INDEPENDENT_FINAL_REVIEW.md), [the exact conditional jet-to-algebraic-root-multiplicity bridge](SP-14/JET_VANISHING_MULTIPLICITY_INDEPENDENT_FINAL_REVIEW.md), [the real upper-triangular base-jet matrix with its unique inverse solve](SP-14/BASE_JET_TRIANGULAR_INDEPENDENT_PARTIAL_REVIEW.md), and [the generic selected-block cofactor identity](SP-14/BASE_JET_CORNER_INDEPENDENT_FINAL_REVIEW.md), and [the exact frozen Fourier-to-matrix bridge for a base plus restored packet](SP-14/BASE_JET_FOURIER_MATRIX_INDEPENDENT_FINAL_REVIEW.md), and [the actual corrected odd-jet polynomial’s finite pencil formula](SP-14/BASE_JET_PENCIL_FORMULA_INDEPENDENT_FINAL_REVIEW.md), and [the explicit real first-jet solve and bijective derivative of that actual base-model map](SP-14/BASE_JET_REAL_SOLVE_INDEPENDENT_FINAL_REVIEW.md) are kernel checked. The base symbol has an outer annular extension and is not the counterexample; selecting correction vectors for perturbed backgrounds, the final infinite symbol, two-sided nonextension, unconditional multiplicity estimates, and final subsequence gap remain unproved in Lean. |
| TR-04 | [`Solution.lean`](../../../tensor-computations/TR-04/lean/Solution.lean) | Elementary candidate/window count inequalities. It explicitly does not prove the TT-SVD approximation target; the current statement has unconstrained rank and operation-count fields. |
| TR-14 | [`WidthBasics.lean`](../../../lean-statements/NLA/Proofs/TR14/WidthBasics.lean) | [Independently reviewed](TR-14/WIDTH_BASICS_INDEPENDENT_FINAL_REVIEW.md) kernel proofs of symmetric-width implies ordinary-width and both exact width-zero characterizations, [moment-index surjectivity and the Hankel-zero equivalence](TR-14/MOMENT_INDEX_INDEPENDENT_FINAL_REVIEW.md), [the exact apolar map and least nonzero degree](TR-14/APOLAR_MINIMAL_INDEPENDENT_FINAL_REVIEW.md), [conditional monic quotient all-moment matching](TR-14/NORMALIZED_QUOTIENT_INDEPENDENT_PARTIAL_REVIEW.md), [the normalized least-apolar quotient’s full Frobenius pairing](TR-14/FROBENIUS_MINIMAL_INDEPENDENT_FINAL_REVIEW.md), [the exact middle catalecticant rank in that monic chart](TR-14/MIDDLE_CATALECTICANT_INDEPENDENT_FINAL_REVIEW.md), and [the genuine homogeneous chart substitution, degreewise equivalence, multiplication, and inverse-dual pairing](TR-14/GL2_HOMOGENEOUS_INDEPENDENT_FINAL_REVIEW.md). The original-coordinate middle catalecticant rank is now proved through the independently reviewed GL₂ chart bridge below. The arbitrary ordinary-to-symmetric implication and full all-width target remain unproved. |

The [independently reviewed MF-03 dense-set cosine product](MF-03/COSINE_DENSE_PRODUCT_INDEPENDENT_FINAL_REVIEW.md)
identifies the factorial wave series with `cos(πw)` and proves convergence
of its finite cosine product when `sin(πw)≠0`. The [all-complex extension](MF-03/COSINE_ALL_COMPLEX_INDEPENDENT_FINAL_REVIEW.md)
now proves the exact positive-factor product value identity and finite-product
convergence for every complex argument. The [independently reviewed coefficient
transfer](MF-03/COSINE_COEFFICIENT_TRANSFER_INDEPENDENT_FINAL_REVIEW.md)
identifies every finite-subset elementary coefficient with the exact factorial
wave coefficient. Schur/Padé denominator bounds and the all-order Target remain open.

The SP-14 partial project also contains the [independently reviewed exact
Sobolev oversampling operator algebra](SP-14/SOBOLEV_OVERSAMPLING_INDEPENDENT_FINAL_REVIEW.md):
it proves the source's displayed right inverse, range, and sharp norm estimate
from explicit two-space bounds. Its actual background-operator hypotheses
remain open.

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
nonnegative output index. Weighted operator estimates remain open.

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

## Shared statement only; no live proof source (34)

The following files define a `Target : Prop` and pass statement-boundary checks.
They do **not** contain a theorem proving `Target`. The source-path pattern is
`lean-statements/NLA/Statements/IDWITHOUTDASH.lean`.

| ID | Statement source | ID | Statement source |
| --- | --- | --- | --- |
| AA-01 | [`AA01.lean`](../../../lean-statements/NLA/Statements/AA01.lean) | AV-01 | [`AV01.lean`](../../../lean-statements/NLA/Statements/AV01.lean) |
| AV-02 | [`AV02.lean`](../../../lean-statements/NLA/Statements/AV02.lean) | FR-10 | [`FR10.lean`](../../../lean-statements/NLA/Statements/FR10.lean) |
| IE-08 | [`IE08.lean`](../../../lean-statements/NLA/Statements/IE08.lean) | IE-10 | [`IE10.lean`](../../../lean-statements/NLA/Statements/IE10.lean) |
| IE-12 | [`IE12.lean`](../../../lean-statements/NLA/Statements/IE12.lean) | IE-26 | [`IE26.lean`](../../../lean-statements/NLA/Statements/IE26.lean) |
| IV-05 | [`IV05.lean`](../../../lean-statements/NLA/Statements/IV05.lean) | MD-03 | [`MD03.lean`](../../../lean-statements/NLA/Statements/MD03.lean) |
| MD-04 | [`MD04.lean`](../../../lean-statements/NLA/Statements/MD04.lean) | | |
| MF-08 | [`MF08.lean`](../../../lean-statements/NLA/Statements/MF08.lean) | MI-16 | [`MI16.lean`](../../../lean-statements/NLA/Statements/MI16.lean) |
| MI-31 | [`MI31.lean`](../../../lean-statements/NLA/Statements/MI31.lean) | NM-03 | [`NM03.lean`](../../../lean-statements/NLA/Statements/NM03.lean) |
| PF-04 | [`PF04.lean`](../../../lean-statements/NLA/Statements/PF04.lean) | PF-05 | [`PF05.lean`](../../../lean-statements/NLA/Statements/PF05.lean) |
| RA-04 | [`RA04.lean`](../../../lean-statements/NLA/Statements/RA04.lean) | RA-05 | [`RA05.lean`](../../../lean-statements/NLA/Statements/RA05.lean) |
| RA-10 | [`RA10.lean`](../../../lean-statements/NLA/Statements/RA10.lean) | | |
| RA-12 | [`RA12.lean`](../../../lean-statements/NLA/Statements/RA12.lean) | RA-13 | [`RA13.lean`](../../../lean-statements/NLA/Statements/RA13.lean) |
| RA-19 | [`RA19.lean`](../../../lean-statements/NLA/Statements/RA19.lean) | RE-05 | [`RE05.lean`](../../../lean-statements/NLA/Statements/RE05.lean) |
| RE-06 | [`RE06.lean`](../../../lean-statements/NLA/Statements/RE06.lean) | SP-11 | [`SP11.lean`](../../../lean-statements/NLA/Statements/SP11.lean) |
| SP-12 | [`SP12.lean`](../../../lean-statements/NLA/Statements/SP12.lean) | SP-13 | [`SP13.lean`](../../../lean-statements/NLA/Statements/SP13.lean) |
| TR-06 | [`TR06.lean`](../../../lean-statements/NLA/Statements/TR06.lean) | TR-08 | [`TR08.lean`](../../../lean-statements/NLA/Statements/TR08.lean) |
| TR-17 | [`TR17.lean`](../../../lean-statements/NLA/Statements/TR17.lean) | | |
| TR-20 | [`TR20.lean`](../../../lean-statements/NLA/Statements/TR20.lean) | TR-21 | [`TR21.lean`](../../../lean-statements/NLA/Statements/TR21.lean) |
| TR-26 | [`TR26.lean`](../../../lean-statements/NLA/Statements/TR26.lean) | | |

LeanCert `#assert_statement`, `#assert_trust kernel`, frozen identity checks,
and the shared Comparator certificates check statement definitions and their
trust closure. They do not prove any of the 34 statement-only propositions or
upgrade the nine partial projects to full proofs.
