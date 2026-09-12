# PR 183 independent singular-value and norm cross-check

**Verdict: PASS. No blocker found in the assigned spectral/norm bridge.**

Reviewer: Codex AI agent `/root/audit_spectral_linear/ie16_pr178`, 12 September 2026.
Exact reviewed head: `1dddf3d17681a91adbcf1dfa43b7ee79653f55fd`.
Read-only checkout: `/private/tmp/nla-audit-183`.
Local file locators below are relative to `matrix-inequalities-and-norms/MI-22/lean/NLA/MI22/`.

I read all of `Definitions.lean`, `SingularValues.lean`, and `Norms.lean`. This is a bounded mathematical/source review; the coordinating reviewers handle the CFC identities, adapted witness, final contradiction, export comparison, trust evidence, and authenticated current CI. No submitted review verdict was used as evidence, and no test or Lean build was run.

## Concrete findings

1. **Actual map and norm, with consistent Euclidean structure.** `Definitions.lean:42–43` defines each singular value as Mathlib's `LinearMap.singularValues` of `Matrix.toEuclideanLin A`. `Definitions.lean:64–65` defines the norm through the genuine complex Euclidean continuous linear map. `Norms.lean:14` explicitly enables `Matrix.Norms.L2Operator`, and `Norms.lean:20–21` identifies the scoped matrix norm with that explicit CLM norm. No assumed list, arbitrary spectrum, entrywise maximum, or unrelated default matrix norm is substituted.

2. **Gram operator and first singular value.** `SingularValues.lean:41–45` proves that the map of `Aᴴ * A` equals the Euclidean adjoint composed with the map of `A`. `SingularValues.lean:19–39` obtains the first ordered eigenvalue of a positive semidefinite matrix from the actual Hermitian spectral theorem, handling the cardinality-index equivalence explicitly. `SingularValues.lean:47–62` combines the squared-singular-value identity with the true C*-norm Gram identity and nonnegativity on both sides. Thus its final equality is the actual first singular value equals the induced operator norm. Squaring has not introduced a sign ambiguity.

3. **Ordering and multiplicity.** `SingularValues.lean:64–78` uses the actual Mathlib family to establish nonnegativity, antitonicity, the full in-dimension Gram-eigenvalue square-root formula, zero extension beyond dimension, and the first-value identity. The underlying eigenfamily is sorted decreasingly and indexed by a full orthonormal eigenbasis. Repeated eigenvalues remain repeated; the definition does not deduplicate roots. `Definitions.lean:47–54` uses the correct first-k range `0,...,k-1`, all proper prefix inequalities, and equality of the complete n-term products.

4. **Frobenius upper bound.** `Definitions.lean:68–69` is the sum of squared complex moduli over every entry. `Norms.lean:52–63` expands the actual Gram trace, exchanges the finite sums, and proves equality with that sum. `Norms.lean:37–50` bounds the operator norm of a PSD matrix by its trace using nonnegative eigenvalues. Together with `Norms.lean:65–67`, this proves `operatorNorm A ^ 2 ≤ frobeniusSquared A` at `Norms.lean:69–77`. The argument is valid for arbitrary complex matrices, including rank-deficient ones.

5. **Coordinate and power bounds.** `Norms.lean:78–80` first bounds a coordinate by the Euclidean vector norm, then uses the CLM operator bound. `Norms.lean:25–27` is genuine operator submultiplicativity. `Norms.lean:82–86` applies the self-adjoint power-of-two norm identity with exponent (2^3=8); Hermitian is sufficient, without an additional positivity premise.

6. **Dimension and rank-zero conventions.** The first-eigenvalue constructions correctly require `1 ≤ n`; no `Fin 0` element is fabricated. The full conjecture already quantifies only positive dimensions (`Definitions.lean:58–60`). Other norm lemmas do not assume a nonempty index type and remain valid at n=0: the zero-dimensional CLM norm, Frobenius sum, and trace are zero, and coordinate assertions are vacuous. At rank zero in a positive dimension, Mathlib's singular family is identically zero, so the norm equality remains valid. For singular matrices of higher rank, all terms from the rank onward vanish. No rank-positivity or generic-eigenvalue premise is silently added. At n=1, the prefix inequalities are correctly empty while the full-product equality is retained; at n=0 the empty prefix product convention is one, but that dimension is outside the conjecture.

## Pinned API inspection

The project manifest pins Mathlib to `0df444a360eaa60ab8c11dca51a86af692955474`, Lean to 4.33.1, and LeanCert to `621a43d7cf21f87872392a01e874f2f1dbddc926`. I found an existing local Mathlib Git object database and read the following files explicitly with `git show` at the **pinned revision**, rather than treating that database's different working-tree HEAD as the project pin:

* `Mathlib/Analysis/CStarAlgebra/Matrix.lean:98–120` constructs the Euclidean CLM via the orthonormal coordinate basis, identifies its underlying linear map with `toEuclideanLin`, and identifies its action with matrix-vector multiplication. Lines 183–246 identify the L2 norm and prove the adjoint-composition, multiplication, and diagonal-norm formulas used here.
* `Mathlib/Analysis/InnerProductSpace/Spectrum.lean:277–315` defines the decreasing eigenfamily and retains eigenspace multiplicities.
* `Mathlib/Analysis/Matrix/Spectrum.lean:56–70,159–178` links the matrix eigenfamilies to the actual Euclidean operator and the full characteristic-root multiset.
* `Mathlib/Analysis/InnerProductSpace/Adjoint.lean:1053–1057` proves the conjugate-transpose/Euclidean-adjoint bridge.

I also read the pinned [Mathlib singular-value source](https://raw.githubusercontent.com/leanprover-community/mathlib4/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/SingularValues.lean), including its definition, square-root and squared-value identities, antitonicity, dimension cutoff, exact support through the rank, and zero-map conventions. These APIs support the submitted source directly.

**Disposition:** the assigned spectral/norm component passes mathematical source review. This report makes no claim of having re-elaborated the proof or authenticated CI. No repository/GitHub changes or checksums were made.
