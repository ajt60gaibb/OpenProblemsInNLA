# Proof inventory for the 46 Solved problems

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
| TR-13 | [`Solution.lean`](../../../tensor-computations/TR-13/lean/Solution.lean) | Exports `NLA.TR13.generic_rank_equality` and the [independently reviewed all-width bridge](TR-13/EXACT_STATEMENT_INDEPENDENT_REVIEW.md) for every odd `m ≥ 5`, `n ≥ 2`, with all five exact generic ranks and equivalence at every natural width. Pinned local LeanCert kernel checks pass with only standard axioms. Isolated Linux Comparator verification of the new bridge remains outstanding. |
| MF-23 | [`CanonicalBridge.lean`](../../../matrix-functions-and-stability/MF-23/lean/CanonicalBridge.lean) | Proves the [reviewed canonical block-order target](MF-23/CANONICAL_BRIDGE_INDEPENDENT_REVIEW.md) from the pinned external `complete_crouzeix` proof by a norm-preserving tensor-factor swap. Its self-contained source-locked project, pinned Lean 4.34.1 build, and LeanCert kernel audit pass locally. Isolated Linux Comparator verification remains outstanding. |
| RA-06 | [`Final.lean`](../../../lean-statements/NLA/Proofs/RA06/Final.lean) | The [independently reviewed full theorem](RA-06/FINAL_INDEPENDENT_REVIEW.md) inhabits the frozen original negative `Target` for every `p > 2`, with the exact sampler, same `α`, expected retained count, and raw log budget. Pinned Lean 4.33.1 aggregate build and independent LeanCert kernel audit pass with only standard axioms. Isolated Linux Comparator verification of the self-contained project remains outstanding. |

## Local partial solution projects (6)

| ID | Live source | What is actually proved |
| --- | --- | --- |
| IE-21 | [`Solution.lean`](../../../linear-systems-and-elimination/IE-21/lean/Solution.lean) | Zero vector and empty row-energy lemmas. The full target is an axiom and the spherical-row law semantics remain unimplemented. |
| IE-22 | [`Solution.lean`](../../../linear-systems-and-elimination/IE-22/lean/Solution.lean) | Zero vector and empty row-energy lemmas. The full target is an axiom; complete semantics and proof remain. |
| IV-02 | [`Solution.lean`](../../../intervals-and-absolute-value-equations/IV-02/lean/Solution.lean) | Rotation identity and positive even layer count. The original complexity claim remains absent from the implemented semantics. |
| IV-04 | [`Solution.lean`](../../../intervals-and-absolute-value-equations/IV-04/lean/Solution.lean) | A two-by-two corner algebra lemma. The original complexity target is absent and the current statement's interval semantics have a known scope gap. |
| MD-06 | [`Solution.lean`](../../../matrix-discrepancy-and-optimization/MD-06/lean/Solution.lean) | Extracts a nonsynchronized critical point from an assumed stable event. Graph probability and local-minimum semantics are parameters of an abstract structure. |
| TR-04 | [`Solution.lean`](../../../tensor-computations/TR-04/lean/Solution.lean) | Elementary candidate/window count inequalities. It explicitly does not prove the TT-SVD approximation target; the current statement has unconstrained rank and operation-count fields. |

## Shared statement only; no live proof source (36)

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
| MD-04 | [`MD04.lean`](../../../lean-statements/NLA/Statements/MD04.lean) | MF-03 | [`MF03.lean`](../../../lean-statements/NLA/Statements/MF03.lean) |
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
| TR-14 | [`TR14.lean`](../../../lean-statements/NLA/Statements/TR14.lean) | TR-17 | [`TR17.lean`](../../../lean-statements/NLA/Statements/TR17.lean) |
| TR-20 | [`TR20.lean`](../../../lean-statements/NLA/Statements/TR20.lean) | TR-21 | [`TR21.lean`](../../../lean-statements/NLA/Statements/TR21.lean) |
| TR-26 | [`TR26.lean`](../../../lean-statements/NLA/Statements/TR26.lean) | | |

LeanCert `#assert_statement`, `#assert_trust kernel`, frozen identity checks,
and the shared Comparator certificates check statement definitions and their
trust closure. They do not prove any of the 36 propositions or upgrade the six
partial projects to full proofs.
