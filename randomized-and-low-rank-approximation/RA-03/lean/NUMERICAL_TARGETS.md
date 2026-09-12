# RA-03 statement boundary and numerical obligations

Status: statements compiled; implementation must wait for two independent statement reviews.

This project formalizes Matthew J. Colbrook's negative resolution of RA-03. The formalization author is George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. The original mathematical counterexample remains attributed to Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. No priority or external human peer-review claim is made.

## Sources and complete target

The canonical source is `randomized-and-low-rank-approximation/RA-03/README.md` at upstream revision `e7252e5307781a7c897bca6cb124f6ab838f6809`. The complete informal manuscript is `references/colbrook-random-pivoting-2026-09-11/manuscripts/sharp_random_pivoting.tex`; all 637 lines were read before this statement draft. The formalized counterexample is its Section 2. The manuscript's stronger sharp factor `4^r` theorem, asymptotic family, and correlation-matrix extension are outside this formalization's scope. The Section 2 counterexample alone settles the full original RA-03 target.

The original algorithm and squared-error formulation were also checked against [Gilles–Wilber, arXiv:2601.22344v1](https://arxiv.org/html/2601.22344v1), equations (1) and (3), Algorithm 1, and Section 2.2. This is randomized **LU** with an entry pivot; the diagonal-pivot Cholesky process in the same Colbrook manuscript concerns RA-02.

The original universal assertion is: for every pair of positive integers `m,n`, every complex `m × n` matrix `A`, and every integer `k` with `1 ≤ k ≤ min(m,n)`, the specified exact-arithmetic process starting at `S₀=A` satisfies

`E[‖Sₖ‖F²] ≤ 2^k ∑_{j>k} σⱼ(A)²`.

At a nonzero residual `S`, a row/column pair `(i,j)` is sampled with conditional probability `|Sᵢⱼ|² / ‖S‖F²`. The update is

`S′ₐᵦ = Sₐᵦ − Sₐⱼ Sᵢᵦ / Sᵢⱼ`.

After reaching the zero matrix, every later residual is zero. No Hermitian, positive-definite, real-entry, nonsingularity, nonzero-entry, or singular-value-separation assumption is added to the universal claim. The concrete witness happens to have several of these properties, but they are not needed as additional premises.

The final export `NLA.RA03.not_squaredErrorConjecture` is the negation of this full assertion, not the negation of a one-step-only or fixed-dimension replacement.

## Exact formal meanings

`NLA/RA03/Definitions.lean` imports only mathlib. It contains no local theorem, axiom, placeholder, or solution import. The following definitions belong to the statement boundary and require independent semantic review before proof.

| Definition | Mathematical meaning |
| --- | --- |
| `frobeniusSq A` | `∑ᵢ ∑ⱼ Complex.normSq(A i j)`, the sum of squared complex moduli. A public theorem will identify this with the square of mathlib's Frobenius norm. |
| `Pivot m n` | `Option (Fin m × Fin n)`. `some (i,j)` is one jointly sampled entry; `none` is the absorbing transition label. |
| `pivotMass S` | At `S=0`, mass one at `none` and zero at all entry labels. At `S≠0`, mass zero at `none` and mass `Complex.normSq(S i j)/frobeniusSq S` at `some (i,j)`. |
| `pivotResidual S (i,j)` | The exact displayed rank-one cross update when the selected entry is nonzero. At a zero entry it returns `S`; this only defines an otherwise unused outcome with selection mass zero. |
| `nextResidual S` | `pivotResidual S (i,j)` for an entry label; zero for `none`. A positive-mass `none` transition is possible only at the zero residual. |
| `historyResidual S h` | The result of following all `k` labels of `h : Fin k → Pivot m n`, updating the actual residual at each step. |
| `historyMass S h` | The product of the actual conditional masses encountered along that history, recursively recomputed from each updated residual. |
| `expectedError A k` | The finite sum over every length-`k` history of its joint mass times the squared Frobenius norm of its terminal residual. This is the expectation of the explicit finite probability law. |
| `singularValue A j` | The actual mathlib singular value `(Matrix.toEuclideanLin A).singularValues j`. Its domain and codomain are complex Euclidean spaces. It is not an arbitrarily supplied spectral list. |
| `singularTailSq A k` | The sum of squares of those singular values for zero-based indices in `Finset.Ico k (min m n)`. This is exactly the paper's one-based tail `j > k` through `min(m,n)`. |
| `SquaredErrorConjecture` | The full quantified canonical inequality stated above. |

The finite probability-law formulation avoids measure-theoretic integration while retaining all conditional sampling semantics. A required public theorem proves that the transition masses and all length-`k` history masses are nonnegative and sum to one, for arbitrary dimensions, inputs, and `k`. The `Option` label also gives a well-defined absorbing law in dimension zero; the canonical conjecture itself quantifies only positive dimensions.

The joint entry pivot is never replaced by independently sampled row and column pivots. Successive choices are not assumed independent. Zero-probability entry updates are totalized explicitly and cannot change the expectation. At a zero matrix the only positive-mass transition stays at zero, so the zero-residual convention is preserved for every `k`.

Mathlib defines singular values in decreasing order, with multiplicity, from the square roots of the eigenvalues of `T.adjoint ∘ₗ T`. Its sequence is zero-indexed and eventually zero. The target uses its literal singular-value tail, so no unproved Eckart–Young equivalence or candidate best-approximation matrix is substituted into the conjecture. The manuscript's statement that the best rank-one squared error is one is represented here by the canonical tail being one, using actual singular values.

## Exact numerical statements to prove

Set `m=n=2`, `k=1`, and

```
A = [[2, 1],
     [1, 2]]  over ℂ, with zero imaginary parts.
```

The witness must be proved nonzero, with all four entries nonzero. Its squared Frobenius norm must be proved to equal `10`. Its actual complex Gram matrix must be proved to equal

```
Aᴴ A = [[5, 4],
        [4, 5]].
```

Its two actual singular values must be proved to be `3` and `1` in that order. In particular, `singularTailSq A 1 = 1`. The Gram characteristic polynomial `(X−9)(X−1)` and exact spectral APIs offer a route to proving the actual ordered squared singular values without numerical square roots. A candidate characteristic polynomial, candidate eigenvalues, or external eigensolver output is not a substitute for this required connection.

All table indices below are Lean's zero-based indices. Each residual is the entire matrix returned by the actual rank-one cross update.

| Pivot `(i,j)` | Conditional probability | Actual residual | Squared Frobenius error |
| --- | --- | --- | --- |
| `(0,0)` | `2/5` | `[[0,0],[0,3/2]]` | `9/4` |
| `(0,1)` | `1/10` | `[[0,0],[-3,0]]` | `9` |
| `(1,0)` | `1/10` | `[[0,-3],[0,0]]` | `9` |
| `(1,1)` | `2/5` | `[[3/2,0],[0,0]]` | `9/4` |

The fifth one-step label, `none`, has probability zero for this nonzero witness. The four displayed entry probabilities must be derived from `pivotMass`, not supplied as a hypothesis. The four residual errors must be derived from `pivotResidual` and `frobeniusSq`, not entered as an unrelated lookup-table expectation. The witness probability/error tables in `Definitions.lean` only name the exact right-hand sides to be proved.

The finite-history expectation must then be proved to equal

`expectedError A 1 = 2·(2/5)·(9/4) + 2·(1/10)·9 = 18/5`.

The exact strict inequality is

`2^1 · singularTailSq A 1 = 2 < 18/5 = expectedError A 1`.

It contradicts the instance `m=n=2`, `A=witness`, `k=1` of `SquaredErrorConjecture`. Both dimension lower bounds, the pivot lower bound, and `1 ≤ min(2,2)` must be discharged in Lean. No external assumption about the witness's spectrum, admissibility, probabilities, update, expectation, or comparison is allowed in the final negative theorem.

## Public statement exports and proof gate

`Challenge.lean` declares four public statements with intentional placeholders:

1. `NLA.RA03.frobeniusSq_eq_norm_sq`: the exact generic Frobenius norm bridge, with mathlib's Frobenius matrix-norm scope explicitly selected.
2. `NLA.RA03.process_isProbability`: the generic transition and history law is nonnegative and normalized for every input and every number of steps.
3. `NLA.RA03.counterexample`: the actual witness, Gram identity, ordered singular values, four probabilities, four residual errors, expected error, tail, and strict reverse inequality hold together.
4. `NLA.RA03.not_squaredErrorConjecture`: the full original universal conjecture is false.

The proof implementation will reproduce these declarations in `Solution.lean`, importing proof-independent definitions and completed proof modules, never `Challenge.lean`. Comparator must check the four target declarations in separate challenge and solution environments. Definitional/theorem-statement matching complements independent semantic review; it cannot establish that the definitions themselves match the informal problem.

**Implementation is prohibited until two independent statement reviews approve the compiled definitions, these numerical obligations, and the Challenge declarations.** Any later change to the statement boundary requires renewed review and new source hashes.

## Computation and trust plan

All matrix and probability calculations concern four entries and four nonzero one-step outcomes. Use exact rational arithmetic and proof-producing finite algebra. Use existing mathlib Euclidean linear-map, adjoint, spectral, finite-sum, and complex-norm APIs. Prove generic finite probability normalization inductively; do not enumerate arbitrary-dimensional histories by computation.

LeanCert's explicit kernel mode will certify only the final rational scalar comparison `2 < 18/5`. There is no interval box to subdivide and no numerical eigensolver, approximate square root, random sampling, or floating-point computation in the certificate. Algebraic and spectral equalities establish the full matrix/algorithm statement to which that scalar comparison applies.

Expected transitive axioms are only `propext`, `Classical.choice`, and `Quot.sound`, or a subset. The final solution must contain no `sorry`, `admit`, unproved custom axiom, `native_decide`, or native execution trust. All public declarations and the LeanCert scalar certificate must pass `#assert_trust kernel` and `#print axioms` checks. A successful build alone will not be represented as final verification; independent final proof referees, Comparator, reproducibility evidence, and the parent workflow's metadata remain required.

The project is pinned to Lean `4.33.1`, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Dependency artifacts were copied into this isolated worktree using APFS clone-copy; the original user cache is not modified.
