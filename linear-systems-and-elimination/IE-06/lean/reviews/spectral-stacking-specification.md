# Singular values, genuine pseudoinverse, and Lemma 4.6: proposed exact contract

This proposal is for coordinator review before implementation. Primary mathematical source: [Urschel, arXiv:2610.06785v1, Lemma 4.6](https://arxiv.org/html/2610.06785v1#S4.L6). The already reviewed full-proof specification supplies the explicit positive denominator guard required by Lean's total division.

## Shared representations

For finite coordinate index types α,β and a real matrix A:Matrix α β ℝ, let `euclideanMap A` be the actual `Matrix.toEuclideanLin A`, acting from EuclideanSpace ℝ β to EuclideanSpace ℝ α. Define `opNorm A` as the induced continuous-linear-map norm. For ordinary Fin dimensions this is definitionally the established `GaussianFrobenius.euclideanOpNorm`.

Define `singularValue A i` to be Mathlib's `LinearMap.singularValues` of this actual Euclidean map. This is the descending **zero-based**, nonnegative sequence, zero after the rank. A source index ℓ≥1 is therefore `singularValue A (ℓ-1)`. Basic wrappers will prove nonnegativity, antitonicity, and positivity exactly for indices below the actual rank.

Define the genuine pseudoinverse on every matrix, including singular matrices, by

`pinv A = Aᴴ * cfc (fun t : ℝ => t⁻¹) (A * Aᴴ)`.

The finite Hermitian spectrum makes every scalar function continuous on that spectrum, and real inversion maps a zero eigenvalue to zero. An explicit spectral diagonalization identity will exhibit this as the Moore–Penrose spectral construction. No ordinary Gram inverse is substituted on singular matrices. Under an explicit positive-definite Gram hypothesis (or its derived full-row-rank equivalent), prove its equality to `Aᴴ * (A*Aᴴ)⁻¹`. The GaussianRegression agent needs the subsequent full-row-rank identity `opNorm (pinv A)^2 = opNorm ((A*Aᴴ)⁻¹)`; the right side is the norm of the matrix inverse, not the reciprocal of the norm.

## Exact stacking target

Let s,k,j:ℕ, M:Matrix (Fin s) (Fin (s+k)) ℝ, Q:Matrix (Fin (s+k)) (Fin k) ℝ, and B:Matrix (Fin k) (Fin (s+k)) ℝ. Assume:

- `Function.Surjective (euclideanMap M)` (full row rank);
- `Qᴴ * Q = 1`, and `LinearMap.range (euclideanMap Q) = LinearMap.ker (euclideanMap M)` (Q's columns are an orthonormal basis of the kernel);
- `2*j < k` and `j < s`;
- `0 < singularValue (B*Q) (k-j-1)`.

The target is

`(opNorm (pinv M) + (1 + singularValue (B*pinv M) j) / singularValue (B*Q) (k-j-1))⁻¹ ≤ singularValue (Matrix.fromRows M B) (s+k-2*j-1)`.

The rows of fromRows are indexed by `Fin s ⊕ Fin k`; their cardinality is s+k. This is the literal vertical stack and its Euclidean coordinate order agrees with the source up to the canonical coordinate isometry. The guards ensure all source indices are positive and valid; no natural subtraction silently changes the target. The positive denominator guard is retained explicitly.

## Proof route and supporting theorem contracts

1. Establish spectral good-subspace statements directly from the orthonormal eigenbasis of the actual adjoint composition and descending eigenvalues. On the span of the first r eigenvectors, the Euclidean norm is bounded below by singular value r−1; on the orthogonal complement of the first j vectors it is bounded above by singular value j. Prove the associated singular-value variational lower bound by the dimension-intersection argument. These are proof obligations, not premises of the public result.
2. In the k-dimensional left row space, intersect the complement of the bottom j left singular directions of BQ with the complement of the top j left singular directions of B pinv(M). This has dimension at least k−2j; select exactly that many orthonormal directions W. Prove the lower bound for Wᴴ BQ and the upper norm bound for Wᴴ B pinv(M).
3. Full-row-rank M gives M pinv(M)=I and M Q=0. The lower bound in step 2 gives a bounded right inverse R for Wᴴ BQ. The concrete solution of the reduced system is x=pinv(M)a + Q R(b−Wᴴ B pinv(M)a). Its norm is bounded by the exact parenthesized constant times sqrt(‖a‖²+‖b‖²), using the triangle inequality and each component norm≤the product-space Euclidean norm.
4. A bounded right inverse yields the smallest-singular-value lower bound of the reduced row system. The orthonormal row projection cannot increase ordered singular values, so the same lower bound holds for source index s+k−2j of the original stack.

No source inequality will be introduced as an axiom, no final target will acquire a spectral/moment hypothesis replacing these obligations, and no stochastic computation is involved. All declarations will receive kernel trust and axiom checks. The source file for singularValues currently supplies order/rank facts but no ready-made full min–max theorem, so step 1 is genuine new infrastructure work.
