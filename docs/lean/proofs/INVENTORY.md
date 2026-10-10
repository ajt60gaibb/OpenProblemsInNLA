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
| MF-03 | [`FiniteRange.lean`](../../../lean-statements/NLA/Proofs/MF03/FiniteRange.lean) | Proves the exact frozen target clause for every order 1–15, including reduced-pair existence and every reduced representative, from [independently reviewed](MF-03/FINITE03_15_INDEPENDENT_REVIEW.md) exact certificates, gcd reduction and disk transport. Separate [all-order cosine-tail](MF-03/COSINE_TAIL_INDEPENDENT_FINAL_REVIEW.md), [value-at-three/numeric-margin](MF-03/WAVE_AT_THREE_INDEPENDENT_FINAL_REVIEW.md), and [complex factor-product convergence](MF-03/COSINE_PRODUCT_INDEPENDENT_PARTIAL_REVIEW.md) lemmas are kernel checked. The series-product identity, orders ≥16, and full all-order target remain unproved. |
| SP-14 | [`SubsequenceGap.lean`](../../../lean-statements/NLA/Proofs/SP14/SubsequenceGap.lean) | [Independently reviewed](SP-14/SUBSEQUENCE_GAP_INDEPENDENT_FINAL_REVIEW.md) kernel proof that a supplied continuous counterexample with a positive eventual empirical gap refutes the exact frozen conjecture. Separate [base-coefficient convolution](SP-14/BASE_COEFFICIENT_INDEPENDENT_REVIEW.md), [unconditional coefficient-defined block product](SP-14/BASE_CB_INDEPENDENT_FINAL_REVIEW.md), [frozen-integral monomial Fourier orthogonality](SP-14/BASE_FOURIER_MODE_INDEPENDENT_REVIEW.md), [absolute summability of the exterior half-binomial coefficients](SP-14/BASE_COEFF_SUMMABLE_INDEPENDENT_REVIEW.md), [continuous exterior boundary series](SP-14/BASE_EXTERIOR_SERIES_INDEPENDENT_REVIEW.md), [termwise frozen Fourier integration](SP-14/BASE_EXTERIOR_FOURIER_INDEPENDENT_REVIEW.md), [the exterior base symbol's exact Fourier pattern and actual odd Toeplitz characteristic polynomial](SP-14/BASE_EXTERIOR_PATTERN_INDEPENDENT_REVIEW.md), [its boundary square and zero identities](SP-14/BASE_EXTERIOR_BOUNDARY_SQUARE_INDEPENDENT_REVIEW.md), [positive packet Fourier support and small-section invisibility](SP-14/POSITIVE_PACKET_INVISIBILITY_INDEPENDENT_FINAL_REVIEW.md), [finite negative-restoration algebra and earlier-section persistence](SP-14/NEGATIVE_RESTORATION_INVISIBILITY_INDEPENDENT_FINAL_REVIEW.md), [the conditional all-order odd-frequency Toeplitz characteristic polynomial in the jet coordinate](SP-14/ODD_FREQUENCY_TOEPLITZ_CHARPOLY_INDEPENDENT_FINAL_REVIEW.md), [continuous odd Fourier support and jet polynomial shape for every finite corrected symbol](SP-14/FINITE_CORRECTED_ODD_SUPPORT_INDEPENDENT_FINAL_REVIEW.md), [the exact conditional jet-to-algebraic-root-multiplicity bridge](SP-14/JET_VANISHING_MULTIPLICITY_INDEPENDENT_FINAL_REVIEW.md), [the real upper-triangular base-jet matrix with its unique inverse solve](SP-14/BASE_JET_TRIANGULAR_INDEPENDENT_PARTIAL_REVIEW.md), and [the generic selected-block cofactor identity](SP-14/BASE_JET_CORNER_INDEPENDENT_FINAL_REVIEW.md), and [the exact frozen Fourier-to-matrix bridge for a base plus restored packet](SP-14/BASE_JET_FOURIER_MATRIX_INDEPENDENT_FINAL_REVIEW.md) are kernel checked. The base symbol has an outer annular extension and is not the counterexample; evaluating the actual corrected jet polynomial, selecting correction vectors, the final infinite symbol, two-sided nonextension, unconditional multiplicity estimates, and final subsequence gap remain unproved in Lean. |
| TR-04 | [`Solution.lean`](../../../tensor-computations/TR-04/lean/Solution.lean) | Elementary candidate/window count inequalities. It explicitly does not prove the TT-SVD approximation target; the current statement has unconstrained rank and operation-count fields. |
| TR-14 | [`WidthBasics.lean`](../../../lean-statements/NLA/Proofs/TR14/WidthBasics.lean) | [Independently reviewed](TR-14/WIDTH_BASICS_INDEPENDENT_FINAL_REVIEW.md) kernel proofs of symmetric-width implies ordinary-width and both exact width-zero characterizations, [moment-index surjectivity and the Hankel-zero equivalence](TR-14/MOMENT_INDEX_INDEPENDENT_FINAL_REVIEW.md), [the exact apolar map and least nonzero degree](TR-14/APOLAR_MINIMAL_INDEPENDENT_FINAL_REVIEW.md), and [conditional monic quotient all-moment matching](TR-14/NORMALIZED_QUOTIENT_INDEPENDENT_PARTIAL_REVIEW.md), and [the normalized least-apolar quotient’s full Frobenius pairing](TR-14/FROBENIUS_MINIMAL_INDEPENDENT_FINAL_REVIEW.md), and [the exact middle catalecticant rank in that monic chart](TR-14/MIDDLE_CATALECTICANT_INDEPENDENT_FINAL_REVIEW.md). The chart transport, original-coordinate middle catalecticant rank, arbitrary ordinary-to-symmetric implication, and full all-width Hankel target remain unproved. |

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
