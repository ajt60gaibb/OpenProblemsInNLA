# RA-08 independent final mathematical review 2

**Verdict: APPROVE the complete frozen mathematics. No unresolved mathematical finding.**

Reviewer: independent AI agent **/root/mf16_final_referee**. I made no RA-08 statement, proof-route or implementation contribution and changed no candidate mathematical file. This review is separate from final referee 1. It is a mathematical and local source-check report, not human peer review, official Tau Ceti endorsement, Linux execution, Comparator execution or permission to publish.

## Exact reviewed inputs

The complete proof freeze, verification/proof-freeze.json, has SHA256
**ab05e2bf801e6906453e88a4d84d5e73191f776db05610fb8b8e5e4a03d4f856**.
It binds **450 project files and 10 original source files** at base
5830ed4fb06da0659414a3deb2a40ad327aca052.
The author handoff has SHA256
dab07a0cf99d739914c54efea282211afcbfb45507ac3fef74b285afc3ad79ce.
I rehashed every bound file before and after fresh checking and at the final seal, checked original Git blobs, and verified complete inventories of both statement-review manifests and both helper-development manifests. All **39 statement-freeze inputs** remain unchanged.

| Boundary or implementation | SHA256 |
| --- | --- |
| Definitions | 8c2f3a76e44730b1f9d5bc8e896070c10868bae817d0c3d11ace22b3c7d94c41 |
| Challenge | 6dfe1fe49431bd3f5dc4c91360911d02c6aaf73d902a40fcabec79155fb11c18 |
| Final proof | 8e225fd88e4fb1d546a26241f835dca9ee08756cc52e3f7fe640ba8b11cf8318 |
| Solution exports | 7dc0f17661a7eead3e4555bbc692ebcc0add5e10b8c6414d51f2cd43c69730cc |
| Comparator configuration | 833d78dcda61a6d240fb1c50dd419ba7f95c3a8ddda768b7e1de6a0047359951 |

I read the complete canonical problem, Colbrook's complete authored manuscript, its historical informal review and attribution record, numerical targets and source correspondence, all sixteen mathematical modules, and all fourteen Solution exports. The historical statement gate and subsequent implementation-role changes are retained; root and the inventory agent later contributed proofs and do not count as independent final referees.

## Mathematical assessment

**Scope and fidelity.** The final proposition negates the entire original assertion: all real dimensions and ranks, both actual symmetric PSD matrices with PSD order, every nonnegative error parameter, every continuous nonnegative nondecreasing concave half-line function, and every ordered orthonormal eigendecomposition. The generic class allows f(0)>0. Function truncation keeps the same selected eigenvectors and zeros omitted coefficients even when f(0)>0. Values outside the half-line are irrelevant by a proved extension-independence theorem. There is no algorithmic approximation restriction, assumed spectrum or hidden desired inequality.

**Selected spectral semantics.** OrderedExistence correctly transports the genuinely sorted eigenvalues₀ through the cardinality equivalence and the inverse of Mathlib's arbitrary eigenvalue reindexing. It reindexes an actual orthonormal eigenbasis and reconstructs the matrix, imposing neither distinct eigenvalues nor positive dimension. The selected columns' orthonormality and eigenvector equations are proved. SpectralCFC constructs a continuous star-algebra homomorphism by evaluation at the selected eigenvalues, diagonal embedding and orthogonal conjugation. Sending the identity to the actual matrix lets CFC uniqueness identify it with Mathlib's genuine CFC. Finiteness makes every bare scalar function continuous on the spectrum, including dimension zero. This is a proved semantic bridge.

**Norm and every-basis tails.** The norm is explicitly that of the Euclidean continuous linear map. The proof uses the actual L2 matrix-norm bridge, unitary invariance and diagonal sup norm. Scalar monotonicity and nonnegativity give the function tail at the first omitted eigenvalue. The Rayleigh inequality uses Euclidean Cauchy–Schwarz and the continuous-linear-map norm, so the transformed difference may be indefinite. Fourth uses nontrivial kernels of a 3-by-4 and a 2-by-3 linear map, proved from finite-dimensional injectivity bounds. Homogeneous quadratic forms establish both inequalities for the fourth eigenvalue for every permitted witness basis. It equals t; the approximation's fourth value is zero. Both approximation truncations and both optimal tails consequently have the required exact values for every selected basis.

**Witness and spectral gap.** The rational 6-by-6 matrix is exactly Colbrook's block projection at t=1/65536. Symmetry and idempotence yield actual Gram-matrix proofs of PSD for the projection and its complement. The positive-definite witness proof forces every coordinate of a hypothetical null vector to zero. Excluding spectrum in (1,17/16) uses an exact complementary compression: the five-coordinate form is at most (b+t) times its squared length, where b+t<1, and the separated diagonal is at least a. The eigenvector cross-term identity forces any alleged gap eigenvector to vanish. The proof converts actual spectrum to a genuine nonzero eigenvector; there is no numerical spectrum premise.

**Minorant and certificate bridge.** Below one, the minorant subtracts a nonnegative square. Above a, the exact shifted polynomial has zero constant coefficient and positive remaining coefficients. The actual cfc_polynomial theorem identifies the matrix polynomial, and cfc_mono uses scalar order on the proved spectrum of the same matrix. It does not assert operator monotonicity of min(x,1). Polynomial interpolation identifies the approximation's genuine image. Three exact matrix-vector products compute K(A)w; symmetry turns the degree-six quadratic form into its squared length. Its value is exactly 26 t (1+gap). Actual matrix order gives the transformed Rayleigh lower bound, and the true norm bound gives strict failure at error zero.

**Material LeanCert and computation size.** The retained numerical_gap_positive_proved calls LeanCert.Validity.verify_strict_upper_bound_dyadic_checked on constant zero and the singleton [0,0], with rational upper bound

78605142319958855341529309 / 11432529876841442781954048000.

Precision is -53 and nominal Taylor depth is 10; no transcendental operation, spectral enclosure or subdivision is evaluated. The actual helper numerical_gap_positive_proved._proof_1_7 is a kernel-reduced Boolean proof using of_decide_eq_true and reflexivity. Its soundness reaches the real strict inequality, Rayleigh contradiction and complete conjecture negation. I inspected the checker, domain-soundness theorem and constant-case evaluator soundness in the pinned library. The unnormalized vector avoids square roots and full degree-six matrix expansion. The weaker positive gap suffices for the complete negative answer; the source's larger contour ratio, Nyström sketch identity and other examples are outside these exports.

## Independent checks

[Fresh-check record](final-referee-2-evidence/fresh-checks.json) records **19 successful commands**: sixteen modules, Solution, separate Challenge, and the final diagnostic. One private empty project prefix excluded all prior RA-08 objects. Ten clean pinned dependency directories were reused read-only from MI-22. No Lake invocation, dependency copying, downloading or rebuilding occurred. Sources, commands, raw logs and generated-object hashes are retained.

The [successful diagnostic log](final-referee-2-evidence/Inspect-retry.log) has SHA256
e133cc4c84306f1222685b9fd287df78181baf521a71f04adf82e9b903092082.
There are **62 axiom reports**, each exactly propext, Classical.choice and Quot.sound, with successful kernel trust assertions. Independent type-and-body traversals check **215 project declarations plus 3 LeanCert soundness declarations from the final target**, and **237 plus 3 from all exports**. Each requires all **41** selected material dependencies, including the actual numerical helper. The inspector rejects unsafe or partial retained declarations, unexplained bodyless declarations and every nonstandard transitive axiom. A fully expanded consumer checks the unrestricted function class, actual PSD order and Euclidean norms against the final negation.

All fourteen normalized Solution signatures exactly match Challenge; the configuration permits no definition exceptions and only the three standard axioms. This comparison and elaboration are **not Comparator execution**. The fourteen deliberate Challenge warnings are isolated; no implementation or successful diagnostic warning occurred.

My [independent rational reconstruction](final-referee-2-evidence/exact-reconstruction.json) has SHA256
312ebde678001aff8cd47a7b8cd6986dcf95393f3634379ef937404f58cbd9a1.
It reads frozen Lean literals using Python fractions and verifies the source block projection, orthonormal columns, exact LDL certificates for PD and relevant PSD/compression forms, all three products, shifted minorant coefficients, approximation interpolation and the exact strictly positive gap. It is supplementary and never a Lean premise.

Reviewer-tool failures remain visible. Two orchestration quoting errors occurred before shell execution. The adapted runner first expected 390 instead of 450 inputs due overlapping text substitutions; its original source and failure are retained. Correcting only that expectation allowed all candidate sources to pass. The first diagnostic's expanded Euclidean-map consumer omitted explicit index/scalar arguments, while both dependency traversals already passed; its full raw failure log and original source remain. Only that reviewer consumer was corrected and rerun in the same fresh prefix. No candidate source or acceptance condition was weakened. Only the reviewer's generated objects were removed after matching their recorded hashes.

## Standards and remaining gates

I applied all ten Tau Ceti angles through the repository protocol: correctness, scope, proof quality, reuse, generality, API design, naming, placement, documentation and attribution. The [primary-input audit](final-referee-2-evidence/primary-and-review-inputs.json) binds thirteen actual library source files, all twelve rubric documents at afb424eda89e8ac96d9eb69f6a88972055a4cd1b, repository policies and the requested Forsythe/Schiffer examples. The retained rubric Git tree was reconstructed and its blobs verified. Those rubric/example materials were read in this agent's preceding independent review and applied here with unchanged pins; source API excerpts were inspected for RA-08. Reused library constructions, scoped modules, names and semantic bridges are suitable for this project. The selected CFC construction credits its Mathlib architecture. An unrelated general-library refactor is not required.

Mathematical source authorship remains **Matthew J. Colbrook**. Formalization author is **George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA**, with disclosed AI assistance. No George email was added. Original licenses and question attribution remain. The registry retains 217 unchanged IDs and RA-08's canonical path and original target.

The frozen live README and metadata are explicitly historical statement-stage inputs, as the handoff explains. Packaging must archive those exact historical bytes and update the live guide and real v0.4 metadata to the completed, truthfully qualified state. That work, final referee 1, authoritative Linux sandbox/controls, actual Comparator and default-kernel replay, independent operational audit and publication review are separate gates. This approval alone does not promote the canonical **Solved** entry to **Lean verified**. I performed no commit, push, PR, source-status change or Linux verification.

[Complete sealed evidence inventory](final-referee-2-evidence/EVIDENCE-MANIFEST.json) binds this report, raw successful and failed checks, source snapshots, diagnostics, primary-input records and final audit.
