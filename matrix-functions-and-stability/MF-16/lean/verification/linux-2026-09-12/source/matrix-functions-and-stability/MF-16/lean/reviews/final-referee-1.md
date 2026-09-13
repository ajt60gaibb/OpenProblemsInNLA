# MF-16 independent final mathematical referee 1

**Verdict: APPROVE the complete frozen mathematics.** All nine exports faithfully prove the required counterexample and negate the complete original complex order-two uniqueness assertion. No mathematical correction is requested. This approval does not replace the remaining Linux Comparator, metadata, operational or publication gates.

Reviewer: `/root/mf16_final_referee`, an OpenAI Codex AI agent. I authored neither the MF-16 statements nor its implementation and made no proof-route contribution. I inspected the source and ran my own checks rather than accepting the author's PASS. My edits are confined to this report and independent review evidence. This is not external human peer review, official Tau Ceti review-service execution, an endorsement by a source author, or certification of historical priority.

## Exact reviewed identity

The proof freeze is `verification/proof-freeze.json`, SHA-256 `f4b21be066d0e55e56aae5b3fd1119433ef09d7ed5822d57dacab906b38ac720`. It binds **182 project inputs and 14 original source files** at base `5830ed4fb06da0659414a3deb2a40ad327aca052`. I rechecked every bound file and original Git blob before and after fresh compilation. All **45 statement-stage inputs** remain byte-identical, including every definition, numerical target, Challenge signature and dependency pin.

| Reviewed input | SHA-256 |
| --- | --- |
| Complete proof handoff | `ad86420d1e3640da6c2edacfc4160a259a766a59764f1f764ca4caa7e1082f78` |
| Statement freeze | `eaba8311f143727f2061f2b4c945e403e62b7e9041712d983ef56ccf2e7f0587` |
| Definitions | `5b8e0a7e11657c6d90dc956664f12f5afefdf8ab556517ae199ab339d99d604e` |
| Challenge | `538b03b014015da03f9929fd520adfb978de96b3fa1b4fe3d995bb94e3dccf0f` |
| Proof | `dbb52d7978f19786503c62cfd17e7ca45dd91c55dd79fae02848967c116b36ed` |
| Solution | `9e7532966e67d32ffc98481b141e2b808a395e3e18645a68aed9a761d19b002b` |

I read the complete canonical target, Colbrook manuscript, its relevant independent informal review and both interval implementations, all project definitions and proof modules, all nine Challenge/Solution signatures, numerical plan, correspondence and final proof map. The earlier statement reports and accepted before-proof gate were also inspected. Their prior approvals do not substitute for this final review.

## Fidelity, non-vacuity and all nine contracts

The actual `WordUniquenessConjecture` quantifies over every finite list of exactly the two constructors X and B, equal to its actual reversal and containing X. For every pair of complex Hermitian positive definite two-by-two B and P, it asserts exactly one complex Hermitian positive definite X with the actual written-order mapped `List.prod` equal to P. No real-only, fixed-word, commuting, diagonal, invertible-only, real-power or extra-letter universal restriction appears.

I inspected Mathlib's actual `Matrix.PosDef` and `ComplexOrder`: positivity concerns the conjugate quadratic form for every nonzero complex vector, with Hermitian symmetry. It is not entrywise positivity or a test restricted to real vectors. A separate freshly checked example consumes the final negation after expanding the word and matrix definitions into that ordinary all-complex proposition.

| Export | Independent assessment |
| --- | --- |
| `word_semantics` | The actual palindrome has 16 letters, 14 X and two B. Natural powers and ordinary matrix multiplication give X B X^12 B X over every semiring, then both advertised real and complex specializations. |
| `source_data` | B=[[1,4],[4,17]], X0=diag(3,1), P=[[4783113,6377496],[6377496,8503345]] are unchanged. Actual multiplication gives the equation, true determinants are 1, 3 and 3^14, and all complex positive-definiteness claims are proved. |
| `twelfth_power_reduction` | The scalar degree-12 remainder identity is applied through genuine `Matrix.aeval_self_charpoly` and `charpoly_fin_two`. The generic helper covers every real two-by-two matrix of determinant three, including nonsymmetric and repeated-eigenvalue cases. No recurrence or diagonalization is assumed. |
| `polynomial_word_equivalence` | All three genuine Expr evaluations are proved equal to the determinant residual and two reduced word residuals. The determinant equation supplies the Cayley–Hamilton hypothesis, yielding an unconditional two-way equivalence with the original word entries. |
| `krawczyk_certificate` | The entire actual LeanCert checker Boolean, exact preconditioner determinant, exact box radius and whole-box contraction bound are proved by `decide +kernel`. |
| `certified_root` | `krawczykCheck_sound` consumes that proof to produce an actual real zero, unique in the closed box. It does not assume a root or infer one from a small sampled residual. |
| `root_to_matrix` | Every certified box root gives x>3, complex Hermitian positive definiteness, equality of every word entry and inequality with X0. |
| `counterexample` | The new complex positive definite matrix and the original X0 are distinct solutions for the same ordinary word and the same positive definite B,P. |
| `not_wordUniquenessConjecture` | Applying the full universal uniqueness assertion to those two solutions gives a contradiction with no additional premise. |

The reduced real matrix is S=[[x,y],[y,z]]. Its determinant-three condition is a conclusion of the first certified equation, not a hidden restriction on the original conjecture. All three variables are independent in the polynomial AST; there is no discarded denominator from the manuscript's two-variable parameterization.

The positive-definiteness bridge is an actual invertible LDL congruence: T=[[1,b/a],[0,1]] and D=diag(a,(ad-b²)/a), with a>0 and ad-b²>0. Its complex image has determinant one, and Mathlib's positive-definite congruence theorem applies to all complex vectors. The algebra proves TᵀDT=[[a,b],[b,d]]. The coordinate box gives the required a>3; determinant three supplies the second positive pivot.

For the unchecked word entry, the proof first establishes actual transpose symmetry and determinant multiplicativity. Thus the word has determinant 3^14 and matching 00 and 01 entries with P. Since P00=4783113>0, the determinant identity fixes the 11 entry. The 10 entry follows from symmetry. Actual matrix ring-homomorphism identities transport multiplication and powers to complex matrices, and equality with X0 would contradict the strict first-coordinate bound. None of these bridges is assumed.

Two solutions suffice to refute the complete canonical claim. The source's three-root count, negative-Jacobian degree argument, exponent-family classification and shortest-word questions are not proved or advertised by these nine exports. Uniqueness within the new root's box is consistent with nonuniqueness of the global matrix equation because X0 is outside that box.

## Actual LeanCert semantics and numerical reduction

I read the complete pinned Krawczyk module and relevant expression, interval, AD-support and trust definitions. The checker verifies supported differentiable expressions, center membership, nonzero actual preconditioner determinant, strict infinity-operator-norm contraction and a strict self-map enclosure. Its soundness proof derives the real Jacobian bound, differentiability, convex closed complete box, Banach fixed point and invertible-preconditioner fixed-point/zero equivalence.

Only const, variables 0/1/2, add, multiply and negate occur in the actual AST. There is one radius-10^-7 rational box, no subdivision and no transcendental approximation. The genuine Cayley–Hamilton reduction avoids interval expansion of the full matrix power; treating the determinant as a third equation avoids inverse-expression AD. This substantially reduces computation without narrowing the universally quantified target.

My fresh inspector serialized the actual AST, center, box, preconditioner, all nine interval Jacobian entries, I−CJ, Newton-center intervals and image intervals. My independent standard-library Fraction/interval-dual implementation imports no submitted Python checker. It reproduced every endpoint exactly and found the same rational contraction bound, approximately 0.02643840048932036, strictly below 27/1000. The preconditioner determinant is exactly

`790668616748253 / 62500000000000000000000000000`.

The center displacement is less than 4×10^-11, and the smallest strict self-map margin is approximately 9.7317056722×10^-8, greater than half the radius. All comparisons use exact fractions; decimal displays are explanatory only. These stronger margins are diagnostics and are not silently added to the export's numerical scope.

A separate sparse-polynomial calculation constructs S^12 and the ordinary word by literal matrix multiplication. It verifies all four Cayley–Hamilton entries modulo xz−y²−3, both actual AST residuals against the reduced word as coefficient identities, every full word entry modulo that determinant relation, the word's symmetry, its determinant identity det(W)=det(S)^14 and the exact remaining-entry recovery formula. The three AST polynomials have 3, 190 and 197 collected terms. These diagnostics support statement fidelity; the Lean proof does not depend on Python.

## Fresh compiled evidence and trust boundary

My independent build started from one empty private project prefix using macOS Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. It freshly compiled Definitions, Numerical, Algebra, Recovery, Polynomial, CayleyHamilton, Proof, Solution and the separate Challenge, then my independent inspector. The ten exact pinned clean MI-22 dependency repositories and dependency objects were reused read-only and rechecked afterward. All earlier MF-16 and MI-22 project objects were excluded. No Lake invocation, dependency copy, download or dependency rebuild occurred.

There are **10 successful source checks** and **26 actual axiom reports**, each containing exactly `propext`, `Classical.choice` and `Quot.sound`. The numerical and exported theorems pass kernel trust assertions. Only Challenge has its nine intentional admission warnings; Solution never imports it. Source scanning and actual compiled declaration inspection found no retained proof admission, custom/native axiom or unsafe/partial project declaration.

The inspector traversed types and proof bodies from the **final negation alone**, reaching **94 project declarations and eight selected LeanCert soundness proofs**. It independently required 30 material dependencies in that closure, including the actual kernel Boolean, certified root, polynomial/CH bridge, complex PD congruence, full word recovery and Banach theorem. Traversing all nine exports reached 110 project declarations plus the same eight library proofs. The actual generated Boolean helper `actual_krawczyk_checked._proof_1_1` occurs in the final proof path. This rules out an unused decorative numerical export.

One initial inspector command failed because my diagnostic JSON serializer used unqualified `toJson`. All candidate compilation commands and both proof-path checks had already passed. I preserved the exact failed inspector, full raw log and command record, changed only that diagnostic call to `Lean.toJson`, and reran the inspector using the same freshly built private candidate objects. No frozen input changed and no proof check was weakened.

A separate read-only rubric audit initially assumed that a retained recursive-tree response's top-level SHA was the tree-object hash. That response is keyed by the requested pinned commit. The corrected audit requires that exact commit key and independently reconstructs every Git tree object, including the root tree `239214b6d320b7d812f8d6547410a0c5625e65ec` referenced by the commit, before matching every rubric blob. The original script, failure and correction are retained; this concerned only reviewer metadata parsing.

All raw successful and failed Lean logs, exact arithmetic results, source hashes, command receipts and checks are in `final-referee-1-evidence/`. After completing the review I removed only this referee's 18 generated objects, each first matched to its recorded hash; all source and evidence and the shared dependency cache remain intact.

## Adapted Tau Ceti assessment and remaining gates

I applied all ten angles through the repository's pinned `docs/lean/REVIEW.md`, reading all twelve complete Tau Ceti rubric files at `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`. Actual hashes and Git blobs are retained. The repository's permanent-ID and original-target rules govern scope; no official Tau Ceti service or roadmap admission is claimed.

Correctness and scope are covered by the full complex statement and each genuine semantic bridge. Proof quality and generality are appropriate: finite algebra is separated from one material certificate, the ordinary word lemma is semiring-generic, and the matrix-power helper has no unnecessary symmetry restriction. The scoped complexification helpers characterize the actual new map and have direct consumers. Searches locate and the proof reuses Mathlib's matrix homomorphisms, Cayley–Hamilton and positive-definite congruence APIs; no directly replacing two-by-two complex leading-minor lemma was located. The definitions, proof modules and nine explicit exports form a readable project interface.

I inspected Schiffer's separate trusted Challenge architecture and Forsythe's Solution/checked-collar and Linux-reproduction patterns at their pinned revisions. These are structural references, not copied Schiffer implementation or independent verification of those projects. The LeanCert Krawczyk example's native proof mode was not imported as the MF-16 proof method.

Attribution is correct: Matthew J. Colbrook retains the mathematical counterexample and Hillar–Johnson/Armstrong–Hillar retain the question's source credit. George Stepaniants receives AI-assisted formalization credit with Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, without a contact email. Existing source authorship is unchanged.

The current README and numerical plan intentionally retain their frozen statement-stage notices, identified as historical in the complete handoff and proof map. Before publication the live README must be updated with an archived original, and truthful v0.4 `formalization.yaml` metadata must be added and validated. The present approval makes no schema-success claim.

The Comparator configuration selects exactly all nine matching Challenge/Solution signatures, permits only the standard three axioms and has no definition exceptions. I checked normalized source signatures and fresh elaboration, **not an actual Comparator run**. Fresh non-root Ubuntu Comparator/default-kernel and actual negative controls, independent operational acceptance, a second independent final mathematical review, and publication review remain required. All 217 permanent IDs, the MF-16 canonical path and original target are unchanged. Canonical status remains Solved.

**No unresolved mathematical finding. Approval applies only to the exact proof freeze above.**
