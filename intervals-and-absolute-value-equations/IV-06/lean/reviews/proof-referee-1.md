# IV-06 independent final proof referee 1

**Verdict: APPROVE / PASS for the complete mathematical formalization.** No mathematical correction is requested. This review does not assert a Linux, Comparator, publication, or official Tau Ceti service result.

Reviewer: `/root/leancert_examples`, an independent AI referee who authored neither the IV-06 statement package nor its proof implementation. The implementation was authored by `/root/solved_statement_inventory`. This review is independent of the author's self-checks and the other final referee. Review date: 12 September 2026.

## Bound candidate and evidence

The reviewed project is `intervals-and-absolute-value-equations/IV-06/lean` in `/tmp/nla-lean-iv06-worktree`. I checked every one of the **126 frozen project inputs**, all **eight original source files**, all **32 statement inputs**, both original independent statement approvals, and the recorded proof-start gate. They remained byte-identical throughout this review. Each original source was also compared with its exact Git blob at `f41f1f9ffa2171550d4bb795862c6170c4f26070`.

| Input | SHA-256 |
| --- | --- |
| `verification/proof-freeze.json` | `5bc8cfd590e82a27807ad5f6832c0cc5d634832979241f80eb30d8d76eaaa673` |
| `reviews/proof-completion.md` | `70aa87f73733ca81dfde6672b4ca09aab90243b3e00111a2cdb20db6f2568a77` |
| `NLA/IV06/Definitions.lean` | `283a31f8e9d100347e5403b8e5688feebd13968d865d487b4962eaa1f861b195` |
| `NLA/IV06/Proof.lean` | `600311e699fecc178f921e8233a9c14d50774db5980ea63560040e578d896333` |
| `Solution.lean` | `b4b9ab44b95accb5f4a0b677d417937cc0ca9ae6c9f08409b2c178ef0d8f699d` |
| `Challenge.lean` | `77be095dc706c901714caa68d3393bf95004fc5f9fee2fa43f7460dafa342b90` |
| `NUMERICAL_TARGETS.md` | `f51f4118af540fa4d3c8e16b40d859ee730c40c8417c4e45f86dc0e5c58a04d9` |
| `SourceCorrespondence.md` | `c7657590d00f5ac46cbf0b30b9edf368f1040b57ea50efae208837f92f0d0408` |
| `comparator.json` | `e84e8d1c516d1ecf17a838d49df61043e90a21a8e72108b285088c02bd35a1c2` |
| Statement referee 1 | `68a4472868bd52e02e0d5ab70f4fb7d5131f3176cc0b8b8c1d1a74b78fd61d48` |
| Statement referee 2 | `b4362f38f8dd4e92bdc24642c734b1ac514e2e39c07592096d5164a1ca601e2e` |

My [evidence manifest](proof-referee-1-evidence/EVIDENCE-MANIFEST.json), SHA-256 **`75c027c684508cc58266da2e893a35405102fa7ebb58bb6f5f9a3cab2c01a38b`**, binds 38 independent scripts, raw logs, inspection sources, diagnostic records, and integrity/API/rubric records. It includes the archived unsuccessful auxiliary diagnostic attempts and excludes only the outer manifest itself. The final independent integrity receipt is [integrity-final.json](proof-referee-1-evidence/integrity-final.json).

## Original target and definition fidelity

I read the complete canonical IV-06 page, the full Colbrook manuscript and original submitted manuscript with its common preamble, the complete informal review, source correspondence, numerical targets, both statement reviews, and every declaration and proof in Definitions, Challenge, Proof and Solution. The original mathematical counterexample remains attributed to **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, receives the separate AI-assisted formalization credit. No George contact email was added.

The complete original universal claim is retained: for every positive dimension and every entrywise ordered pair of real matrix endpoints, the union of real eigenvalues of **all matrices in the full independent-entry box** has at most the dimension many connected components. Singleton entry intervals are allowed. The definition does not assume symmetry, diagonalizability, compactness, a finite component set, or realness of all eigenvalues.

An attained real eigenvalue means an actual nonzero real eigenvector. `characteristicDet` is the actual determinant of `lambda • 1 - A`. The proof of equivalence uses Mathlib's `Matrix.exists_mulVec_eq_zero_iff` and ordinary matrix-vector algebra, without a nonempty-index assumption. My independent inspector additionally checked the empty-index boundary: no nonzero empty vector exists and the determinant of the empty characteristic matrix is one. The original conjecture still quantifies only over positive dimensions.

The attained eigenvalue set carries the inherited topology of the ordinary real numbers. Inspection confirms that the real distance is `|x-y|`, and that `ConnectedComponents` is Mathlib's actual quotient by equality of connected components. The component bound uses actual `Cardinal` order. It cannot pass by converting an infinite set to a natural-cardinality default of zero.

All eight complete Solution signatures exactly match the approved Challenge signatures. The comparator configuration selects precisely those eight exports, lists no replaceable definitions, and permits exactly `propext`, `Classical.choice`, and `Quot.sound`. The final `not_componentBoundConjecture` theorem negates the full original universal claim. Proving at least four components for one admissible dimension-three box is sufficient; the package correctly makes no claim of exactly four components or a complete endpoint classification.

## Mathematical proof inspection and independent reconstruction

The family is

\[
 A(a,b)=\begin{pmatrix}25&a&b\\1&-1&0\\1&0&1\end{pmatrix},
 \qquad -166\le a\le-16,\quad9\le b\le159.
\]

The full-box equivalence is proved in both directions. The seven singleton entries are forced by their lower and upper inequalities; the two remaining entries vary independently through the displayed intervals. No relation between them is silently imposed.

The actual determinant expansion is proved for every real `a`, `b`, and `lambda`:

\[
 \det(\lambda I-A(a,b))=(\lambda-25)(\lambda^2-1)-a(\lambda-1)-b(\lambda+1).
\]

The centered form in the manuscript is also derived exactly. My independently written sparse integer-polynomial diagnostic expanded the six determinant permutations and checked both polynomial identities, without calling the submission's checker.

The four included values are witnessed by these actual nonzero eigenvectors:

| Eigenvalue | `a` | `b` | Vector | Actual matrix-vector product |
| --- | ---: | ---: | --- | --- |
| `-3` | `-21` | `154` | `(-4,2,1)` | `(12,-6,-3)` |
| `0` | `-16` | `9` | `(-1,-1,1)` | `(0,0,0)` |
| `3` | `-146` | `29` | `(4,1,2)` | `(12,3,6)` |
| `25` | `-91` | `84` | `(312,12,13)` | `(7800,300,325)` |

All four matrices satisfy the complete box constraints. These exact data agree with both the Lean definitions and the printed source table. The zero eigenvalue uses a nonzero vector and is not an accidental zero-vector witness.

At the three separating values, the actual determinants reduce to affine functions over the complete parameter rectangle:

| Separator | Determinant | Exact lower bound | Exact upper bound |
| --- | --- | ---: | ---: |
| `-1` | `2a` | `-332` | `-32` |
| `1` | `-2b` | `-318` | `-18` |
| `12` | `-1859-11a-13b` | `-3750` | `-150` |

The Lean proof derives these bounds from the four parameter inequalities. My independent reconstruction checked all twelve corner values **and** the exact nonnegative-distance decompositions establishing the universal affine bounds. It therefore checks the reason the corner bounds extend over the entire box. Finite diagnostics supplement the Lean proof; they do not replace its universal inference.

For a general subset `S` of the reals, equality of the actual connected-component classes of `x,y : S` gives membership in a common actual component. Its image under `Subtype.val` is preconnected by `IsPreconnected.image` and `continuous_subtype_val`. Mathlib's `IsPreconnected.Icc_subset` then places every real intermediate point in `S`. This argument assumes neither that `S` is closed nor that it has finitely many components.

The proof supplies a strictly intervening excluded separator for every ordered pair of the four included eigenvalues. Trichotomy handles both orders in the injectivity argument. Consequently the actual component-class map from `Fin 4` is injective. `Cardinal.mk_le_of_injective`, `Cardinal.mk_fintype`, and `Fintype.card_fin` establish the cardinal lower bound. The resulting strict `3 < componentCardinality` contradicts the original universal bound at dimension three. My actual declaration traversal confirms that these generic topology/cardinality bridges are consumed by the final negation.

## Fresh checking and actual trust dependencies

I independently re-elaborated Definitions, Proof and Solution into a newly created IV-06 prefix, then separately rechecked Challenge and my semantic/dependency inspector. All five commands passed. A sixth command independently inspected and rechecked the exact retained LeanCert Boolean certificate. [The full fresh command record](proof-referee-1-evidence/fresh-checks.json) records source, executable, arguments, environment, elapsed time, raw log hashes and fresh object hashes; [the sixth command](proof-referee-1-evidence/certificate-check.json) is recorded separately.

This used Lean **4.33.1**, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, on macOS ARM64. It reused only the disclosed read-only MI-22 dependency cache, with all ten exact source pins checked clean. Old IV-06 and MI-22 project objects were excluded from `LEAN_PATH`. The fresh project prefix was `/private/tmp/nla-lean-iv06-worktree/intervals-and-absolute-value-equations/IV-06/lean/.verification/iv06-final-referee1-091c7q32`. Dependencies were not rebuilt from source; Lake and the Linux Comparator were not run in this review.

The eight intentional Challenge placeholders were the only warnings. Complete proof modules and Solution contain no `sorry`, `admit`, added `axiom`, `native_decide`, or `unsafe`, and Solution does not import Challenge. All **17 candidate kernel/axiom audits** reported precisely the standard three axioms. My own traversal inspected **58 reached project declarations** from the full negation and required **23 actual material dependencies**, including the determinant, preconnectedness, continuous subtype map, interval containment, cardinal embedding and LeanCert soundness theorem. This is inspection of the elaborated declarations and their bodies, not a search for unused theorem names.

The numerical certificate is material: explicit `interval_decide (trust := kernel)` proves `(-18 : Real) < 0` on the singleton domain `[0,0]`; all three upper bounds are at most `-18`. The checked Boolean uses the exact `Rat.divInt` arguments, precision `-53`, and Taylor-depth argument `10`. The retained helper `NLA.IV06.numerical_separator_margin._proof_1_7` contains `of_decide_eq_true` with kernel-reduced reflexivity evidence. My additional audit of that actual helper reports only the standard three axioms, and an independent repetition with `decide +kernel` passed. The final proof consumes the certificate through separator exclusion, component separation and the cardinal contradiction. No numerical search, interval subdivision, or native execution trust is used.

The pinned LeanCert checker soundness, explicit kernel closure and trust audit, and Lean's `decide +kernel` implementation were inspected in their actual primary source. A source comment describing optional native evaluation does not describe this proof's chosen trust mode. Exact source hashes and links for twelve relevant Mathlib/LeanCert/Lean API files are retained in [api-source-inputs.json](proof-referee-1-evidence/api-source-inputs.json).

Several initial **reviewer-only** diagnostics needed corrections: an unanchored source-signature regex matched a word in a comment, a manuscript-table regex required an optional final row terminator, and certificate pretty-print/reduction checks needed the actual fully elaborated syntax and explicit kernel mode. Their scripts/results are archived. These did not change or reject any candidate statement or proof; all corrected checks passed.

## Adapted referee standards and findings

I applied all ten retained Tau Ceti review angles at pin `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`, using the repository's `docs/lean/REVIEW.md` adaptation. [rubric-inputs.json](proof-referee-1-evidence/rubric-inputs.json) binds each rubric to its exact source blob and records the local adaptation hash. This is an independent application of those standards, not an official Tau Ceti review service.

| Angle | Finding |
| --- | --- |
| Correctness | PASS: all source builds, exact algebra, actual dependencies and kernel checks passed. |
| Scope | PASS: the full independent-entry real matrix-box conjecture is negated, with no extra premise. |
| Proof quality | PASS: exact universal algebra and generic topology/cardinality arguments support the finite witness. |
| Reuse | PASS: actual Mathlib determinant, singularity, connectedness and cardinal APIs are used. |
| Generality | PASS: the determinant bridge includes dimension zero and the component-interval lemma covers arbitrary real subsets; no unnecessary general theorem is claimed. |
| API design | PASS: eight explicit exports separate semantics, witness, topology, cardinality and full negation. |
| Naming | PASS: names are scoped to `NLA.IV06` and describe the actual mathematical role. |
| Placement | PASS: complete proofs are separate from the frozen statement Challenge and original source documents. |
| Documentation | Mathematical scope/correspondence PASS; one historical packaging note below must be refreshed before publication. |
| Attribution | PASS: Colbrook's mathematical authorship and George's approved formalization affiliation remain distinct. |

**D1 — publication documentation only, nonblocking for mathematical approval.** The frozen Lean README is explicitly a statement-stage artifact and still says that no proof exists and both statement reviews are pending. These statements are now historical. Preserve its reviewed bytes and archive/refresh the current README during candidate packaging, accurately reporting complete proofs and completed reviews while keeping Linux/Comparator verification pending until actual audited success. Do not present that historical README as the current verification status. I made no metadata or source changes.

All required mathematical exports are complete. The next independent final referee, packaging/schema checks, actual Linux/default-kernel/Comparator run and negative controls, independent operational audit, and any canonical promotion remain separate gates controlled by the parent. This PASS authorizes none of those results by inference.
