# MI-07 independent statement referee 2

Date: 2026-09-12. Reviewer: OpenAI Codex AI agent `/root`, independent of the statement/proof author. **Verdict: approve this frozen boundary for proof implementation.** Referee 1 has separately approved it. This is a statement review, not completed proof verification or human peer review.

I read the entire canonical README, complete Colbrook solution TeX and submission Markdown, all Definitions, seven Challenge signatures and the complete numerical plan. The three source files match immutable upstream revision `e7252e5307781a7c897bca6cb124f6ab838f6809` exactly. The new upstream math-rendering changes do not authorize changing the mathematical target.

## Complete original assertion

`TriangleConjecture` retains all positive dimensions, all square complex A,B, and existence of two arbitrary complex unitary matrices. No Hermitian, real, rank-one or commutation restriction is imposed on those universal matrices. The right side conjugates the two actual maximal moduli by independently chosen unitaries. The inspected Mathlib unitary group is defined by the true star-inverse identities; the matrix star is conjugate transpose. The scoped `MatrixOrder` comparison is exactly positive semidefiniteness of right minus left. It is not entrywise or spectral order.

The target is the original constant-one assertion. A fixed two-dimensional witness refutes it completely. The stronger source claim that no finite constant works is deliberately excluded, and the selected statements must not later be presented as proving that parameter-family strengthening.

## Actual functional calculus and limits

The ordinary modulus is actual `CFC.abs`, definitionally the positive CFC square root of XᴴX. The first export requires that identity and positivity for every X. The sequence uses genuine matrix-ring powers at every positive integer m=r+1, followed by the explicitly named real `CFC.rpow` at exponent 1/m. This avoids both the nonexistent reciprocal of the initial index zero and an accidental pointwise matrix power.

`Filter.limUnder` is totalized outside convergence. The present negative answer cannot exploit that default: the seven selected exports require actual sequence convergence at each of A, B and A+B, plus a generic identification of a proved limit with `maximalModulus`. No convergence premise is inserted into the conjecture, counterexample or final negation. Every maximal-modulus value involved in the contradiction will therefore be the unique genuine limit. A generic existence theorem for unrelated matrices is not necessary to validate this explicit negative answer and is not claimed by this certificate. Final review must check that the complete counterexample uses these proved limits.

I inspected Mathlib's `Filter.Tendsto.limUnder_eq` in its Hausdorff setting. The finite complex matrix space is Hausdorff and the natural-number atTop filter is nontrivial, so the identification has no hidden ambiguity. I also inspected `Matrix.instL2OpMetricSpace`, which induces the Euclidean operator norm while explicitly retaining the ordinary finite-dimensional topology. The elaborated `spectralNorm` uses the scoped L2 operator-norm instance. The separate norm-convergence equivalence export ensures the stated topology is explicitly tied to genuine spectral norm, rather than relying on a default entrywise norm.

The limit at the rank-one projection needs care: a singular matrix's CFC power at exponent zero is not the limit of its positive powers on the nullspace. The stated A-limit is correctly P, obtained from the actual positive-exponent identity `(2P)^(1/m)=2^(1/m)P`, not an invalid continuity-at-zero argument for the whole singular matrix. For the sum witness the spanning matrix is strictly positive definite, where continuity of positive spectral values at exponent zero is legitimate. The finite identities, positivity and reciprocal-exponent limits all remain proof obligations.

## Independent exact numerical check

I independently reconstructed the rational specialization t=5/12, s=13/12 from the original source family using generic Python `Fraction` matrix products, transpose, determinant and trace. The normalized direction is (12/13,5/13). Its actual outer-product matrix Q satisfies Q²=Q; P²=P; and R=P+Q has first principal entry 313/169 and determinant 25/169. The positive-definite claim is therefore numerically sound in the complex Hermitian setting.

The candidate right/left moduli square to the actual Gram matrices of B and A+B in the correct order. In particular `(sQ)²=(A+B)ᴴ(A+B)` and `(sP)²=(A+B)(A+B)ᴴ`. The polar identities themselves must still be proved from positive square-root uniqueness in Lean, rather than assumed from these checks.

The candidate true limits give trace 13/6 on the left and 11/6 for every two-unitary orbit sum on the right. Cyclic trace and the unitary identities justify independence from U,V. The difference right minus left has exact trace −1/3 and hence cannot be PSD. This excludes all complex unitary pairs and provides a valid original-target refutation. One explicit kernel LeanCert certificate for the strict scalar gap is sufficient; there is no need for interval subdivision, a numerical eigensolver or optimization over unitary matrices. The independent reconstruction is retained as statement evidence and supplies no Lean assumption.

## Actual checks and approval conditions

I independently re-elaborated Definitions and Challenge into a separate output directory and then inspected fully elaborated statements using those fresh files. All three Lean commands exited zero, with exactly seven intentional isolated Challenge placeholders and no proof implementation present. The postprocessing warning counter initially expected single quotes while Lean emits backticks; the corrected parser checks the unchanged raw logs. This affected no statement or Lean command. [Commands, raw logs, source identities and exact reconstruction](statement-referee-2-evidence/) are retained.

The elaborated target uses the real CFC, matrix natural-power, L2-norm, unitary and PSD-order instances inspected above. All frozen source/pin hashes remain unchanged. Two independent final proof reviewers and actual Linux Comparator still must check the completed seven exports, with no definition holes and a transitive axiom set contained in `propext`, `Classical.choice`, `Quot.sound`. Challenge must never be imported by Solution.

Matthew J. Colbrook retains mathematical authorship. George Stepaniants is credited for formalization with the approved Department of Computing and Mathematical Sciences, California Institute of Technology affiliation. AI assistance is disclosed; no George email or human endorsement is introduced. No statement correction is requested.

| Frozen input | SHA256 |
|---|---|
| `NLA/MI07/Definitions.lean` | `369e99eaf3df8a8bbfb214973129ab71fbc95445ba9d176e91d52bca3bc46bc5` |
| `Challenge.lean` | `62fee2804dc12a4ad7edecfa8c1dda2dc39acc2d94475d29805e8e55c3288a59` |
| `NUMERICAL_TARGETS.md` | `70272f54de929a95347db186b09b66d534313eed87ab7daa8e7fe5c8aaa8bd1e` |

Any substantive change to these statements reopens both reviews before implementation.
