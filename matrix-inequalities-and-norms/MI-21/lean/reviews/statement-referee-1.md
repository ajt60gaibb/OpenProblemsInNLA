# MI-21 independent statement referee 1

Date: 2026-09-12. Reviewer: OpenAI Codex AI agent `/root`, independent of the statement/proof author. **Verdict: approve this frozen boundary for proof implementation.** A separate referee 2 approval is already recorded. This is statement review, not a completed proof or external human peer review.

I read the complete canonical README, complete Colbrook solution TeX, all definitions, three Challenge exports and the full numerical plan. The source README, TeX and submission Markdown were independently compared byte-for-byte with upstream revision `e7252e5307781a7c897bca6cb124f6ab838f6809`; their identity record is retained. Subsequent upstream math-rendering changes do not change the target or justify altering these frozen mathematical statements.

## Full original quantifiers and norms

The target preserves every positive matrix dimension and number of summands, all positive definite complex matrix families Aᵢ,Bᵢ, every real t in the closed interval [0,1], every positive real s,r,p with sr≥1, and every unitarily invariant complex matrix norm. It retains the actual sums, real powers, geometric means and the order of noncommuting factors. In particular the right exponents are `(1-t)srp/2`, `tsrp`, `(1-t)srp/2`, followed by the real outer power `1/p`. No known restricted parameter regime replaces the canonical assertion.

`IsUnitaryInvariantNorm` spells out the complete ordinary norm properties: nonnegativity, definiteness, triangle inequality, and absolute homogeneity for every complex scalar. Its invariance has independent left and right unitary factors, with both inverse identities explicitly required. These are exactly true unitary matrices, not only real orthogonal or conjugating factors. Every genuine unitarily invariant norm satisfies this predicate; the target does not quantify only over a chosen norm implementation.

The selected `operatorNorm` is the genuine operator norm of `Matrix.toEuclideanCLM` on complex Euclidean space. I inspected its Mathlib definition as the star-algebra equivalence induced by the orthonormal standard basis, together with the actual matrix-vector action lemma and its L2 operator-norm identity. The generic admissibility export must prove every norm axiom and both-sided unitary invariance for this concrete function in all dimensions, including the harmless zero-dimensional supporting case. No norm property or eigenvalue bound is supplied as a hypothesis to the counterexample.

## Actual analytic definitions

`CFC.rpow` is the real spectral functional calculus, explicitly named to avoid the pointwise power instance inherited from the function representation of a matrix. The weighted mean uses A^(1/2), A^(−1/2)BA^(−1/2), its real t-power, and the final A^(1/2) in the original order. Strict positive definiteness is the complex Hermitian quadratic-form notion. The original hypotheses ensure the intended positive matrix powers are the canonical ones; the candidate equalities needed at the witness are substantive proof obligations.

The three selected exports require a complete counterexample for every p>0 and an unconditional negation of the full norm-quantified conjecture. The rational candidate L is explicitly a definition to be identified with the actual CFC expression, not a substitute definition for that expression. Both actual aggregate identities, all four input positivity facts, actual right-side identity, the nonzero eigenvector equation and the operator-norm lower bound are required consequences. No supplied root, analytic formula, spectral list, determinant or computed value has been inserted as an assumption.

## Independent exact numerical reconstruction

Starting from the source C,E,S, I independently reconstructed generic 2×2 products, inverses, determinants and traces with Python `Fraction`. C and E have positive diagonal entries; S is exactly symmetric and involutory; C²+E²=I. All four input matrices are symmetric with positive leading principal entry and determinant, and both sums are exactly I. Thus the proposed complex positive-definite hypotheses are numerically consistent.

For D=SES, I computed δ=5/3, h=61697295/8682716 and K=D+δC. The exact scaled Riccati equation `K C⁻¹ K=hD` holds. I independently computed the second mean's corresponding equation using E, SCS and δ=3/5. Squaring and dividing by the respective h values gives both rational squared-mean candidates; the second equals S times the first times S. Their sum is exactly the proposed L with denominator 12158163. These checks support a square-root uniqueness proof, but do not assume that the CFC geometric mean equals the candidate. That analytic equality remains mandatory in Lean.

The exact vector w=(1,−4) is nonzero and satisfies Lw=(1351000/1350907)w. The eigenvalue gap is exactly 93/1350907>0. The genuine operator norm must be connected to this Euclidean eigenvector to derive the lower bound; no guessed maximum eigenvalue or numerical eigensolver is needed. Since the right matrix is actually I for every positive p, its norm is one. A single retained explicit kernel LeanCert point certificate for the eigenvalue gap suffices after all the analytic and rational equalities have been proved. There is no reason for interval subdivision, approximate roots or a large parameter computation.

The proposed witness has m=n=2, s=t=1/2, r=2, so all original restrictions hold and sr=1. Choosing this admissible operator norm and any positive p refutes the full universal target, while the stronger witness export correctly states all p>0. The formalization makes no claim against the narrower previously proved regimes in the references and no historical priority claim.

## Actual checks and approval boundary

I independently re-elaborated Definitions and Challenge into a fresh local statement directory and inspected fully elaborated definitions and signatures using those fresh artifacts. All three commands exited zero, with exactly three intentional Challenge placeholders. The inspection identifies actual CFC powers, the complex Euclidean continuous-linear-map norm, matrix multiplication, PSD definitions and the complete universal predicate. No Proof or Solution existed when this review was completed.

[The independent command logs, source hashes and rational reconstruction](statement-referee-1-evidence/) are retained. These are macOS statement checks, not Linux proof verification. All three frozen mathematical inputs remain unchanged. Proof work may now begin because both independent statement reviews approve the same bytes. After implementation, two independent final proof reviewers and actual Linux Comparator must still check all three exports, with no definition holes and only a subset of `propext`, `Classical.choice`, `Quot.sound` in their transitive axioms. Solution must never import Challenge.

Matthew J. Colbrook retains mathematical authorship. George Stepaniants is credited for formalization with the approved Department of Computing and Mathematical Sciences, California Institute of Technology affiliation. AI-agent assistance is disclosed without publishing George's email or implying human endorsement. No statement correction is requested.

| Frozen input | SHA256 |
|---|---|
| `NLA/MI21/Definitions.lean` | `18ebd6d65063b6e970d76b60aab6a8a8bc595189e9b8e188895030d2172f1055` |
| `Challenge.lean` | `f7dd628a7635e8860dec64460bd53adfa71ca391eec763391ae1c8e58d1588b4` |
| `NUMERICAL_TARGETS.md` | `4b0582a3c2da02abf7a349e4ab4af682f6b29bf7026bff21d53edff3ab216312` |

Substantive changes to the frozen mathematical boundary reopen the statement-review gate.
