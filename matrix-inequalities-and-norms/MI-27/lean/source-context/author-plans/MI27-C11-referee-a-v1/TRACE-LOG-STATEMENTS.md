# MI27 C11: trace-log and resolvent bridge, before implementation

Author: `/root/nr04_mf14_final_referee_a`. These are eight proposed exact
helper headers, with no proof bodies written. Root alone runs Lean. The
frozen original C11 theorem and its definitions are unchanged. This plan
requires root and independent nonauthor statement review before bodies.

This component identifies the finite scalar pencil sum with the already
compiled identity-shift kernel. It uses two different sorts of invariance:
determinants for traces of logarithms, and cyclic trace for the rational
resolvent term. No matrix logarithm congruence law, commutativity of X and Y,
or simultaneous eigenbasis is asserted.

The existing shared definitions are literal: `trR M = (Matrix.trace M).re`,
`logM M = CFC.log M`, and `c11_identityShift X r = X + (r : ℂ) • 1`.
The already compiled `c11_shiftKernel` remains its explicit double spectral
sum with the actual unitary overlap weights from the two separate spectra.
This plan introduces no new definitions.

## Exact headers

Namespace `NLA.MI27`; open scoped BigOperators, Classical, ComplexOrder,
MatrixOrder, Matrix, and Matrix.Norms.L2Operator. The intended module is
`NLA.MI27.PencilTraceLog`, importing the accepted identity-shift component
and the necessary pinned Mathlib matrix-inverse APIs.

```lean
lemma c11_identityShift_posDef {n : ℕ} (X : Mat n) (hX : X.PosDef)
    (r : ℝ) (hr : 0 ≤ r) :
    (c11_identityShift X r).PosDef

lemma c11_inv_eq_cfc {n : ℕ} (M : Mat n) (hM : M.IsHermitian)
    (hunit : IsUnit M) :
    M⁻¹ = cfc (fun x : ℝ => x⁻¹) M

lemma c11_trR_log_eq_log_det {n : ℕ} (hn : 1 ≤ n) (P : Mat n)
    (hP : P.PosDef) :
    trR (logM P) = Real.log (Matrix.det P).re

lemma c11_trR_log_normalized_congruence {n : ℕ} (hn : 1 ≤ n)
    (P Q S : Mat n) (hP : P.PosDef) (hQ : Q.PosDef) (hS : IsUnit S)
    (hSP : Sᴴ * P * S = 1) :
    trR (logM (Sᴴ * Q * S)) = trR (logM Q) - trR (logM P)

lemma c11_trR_congruence_mul_inv {n : ℕ} (A B S : Mat n)
    (hB : IsUnit B) (hS : IsUnit S) :
    trR ((Sᴴ * A * S) * (Sᴴ * B * S)⁻¹) = trR (A * B⁻¹)

lemma c11_shiftKernel_eq_trace_log_resolvent {n : ℕ} (hn : 1 ≤ n)
    (X Y : Mat n) (hX : X.PosDef) (hY : Y.PosDef) (r : ℝ) (hr : 0 ≤ r) :
    c11_shiftKernel X Y hX.isHermitian hY.isHermitian r =
      trR (logM (c11_identityShift Y r)) -
        trR (logM (c11_identityShift X r)) -
          trR ((Y - X) * (c11_identityShift Y r)⁻¹)

lemma c11_trace_log_resolvent_spectral {n : ℕ} (hn : 1 ≤ n)
    (C : Mat n) (hC : C.IsHermitian) (h1C : (1 + C).PosDef) :
    (∀ i : Fin n, -1 < hC.eigenvalues i) ∧
      trR (logM (1 + C)) - trR (C * (1 + C)⁻¹) =
        ∑ i : Fin n,
          (Real.log (1 + hC.eigenvalues i) -
            hC.eigenvalues i / (1 + hC.eigenvalues i))

lemma c11_normalized_pencil_trace_kernel {n : ℕ} (hn : 1 ≤ n)
    (X Y : Mat n) (hX : X.PosDef) (hY : Y.PosDef) (r : ℝ) (hr : 0 ≤ r)
    (S : Mat n) (hS : IsUnit S)
    (hSP : Sᴴ * c11_identityShift X r * S = 1) :
    (1 + Sᴴ * (Y - X) * S).PosDef ∧
      trR (logM (1 + Sᴴ * (Y - X) * S)) -
          trR ((Sᴴ * (Y - X) * S) * (1 + Sᴴ * (Y - X) * S)⁻¹) =
        c11_shiftKernel X Y hX.isHermitian hY.isHermitian r
```

## Mathematical route for review

1. A nonnegative scalar identity shift of a positive-definite matrix is
   positive definite. This holds also at r=0. The general inverse helper
   expressly requires invertibility: the nonsingular inverse of a singular
   matrix cannot in general be identified with pointwise reciprocal CFC.

2. For P positive definite, its real determinant is the product of its
   strictly positive eigenvalues. The existing C02 spectral trace theorem
   gives tr(log P) as the sum of their scalar logarithms; `Real.log_prod`
   gives the determinant formula. Thus all scalar log product/division
   applications have nonzero, in fact positive, arguments.

3. Put k = det(Sᴴ) det(S). Taking determinants in Sᴴ P S = I gives
   k det(P) = 1. Hence det(Sᴴ Q S) = det(Q)/det(P). The congruence of Q is
   positive definite because S is invertible. Taking real logarithms and
   using the preceding determinant formula gives the normalized trace-log
   identity. This is a trace identity only.

4. Expanding the inverse of Sᴴ B S gives
   S⁻¹ B⁻¹ (Sᴴ)⁻¹. Cancelling S S⁻¹ and using cyclic trace leaves tr(A B⁻¹).
   A need not be Hermitian and no positivity of B is needed beyond its
   stated invertibility. This keeps the algebraic lemma independent of
   any spectral or entropy assertion.

5. For the kernel identity, express the inverse of Y+rI as CFC of
   x ↦ 1/(x+r) on Y, using inverse CFC and identity-shift composition.
   The existing C16 two-basis product theorem expands
   tr((Y-X)(Y+rI)⁻¹). The row and column sums of the actual overlap weights
   identify the two logarithm terms. This is exactly the negative of the
   already compiled derivative expression. The sign is
   tr(log(Y+rI)) - tr(log(X+rI)) - tr((Y-X)(Y+rI)⁻¹).

6. For Hermitian C, functional calculus for 1+C uses the same eigenbasis
   as C. Positivity of 1+C implies 1+c_i>0, so every c_i>-1, including
   possible negative or zero values of c_i. Trace CFC and the same-basis
   product theorem give the spectral logarithm-minus-resolvent sum. No
   eigenvalues of C are required to be nonzero or distinct.

7. Finally, with P=X+rI, Q=Y+rI and C=Sᴴ(Y-X)S, expand to obtain
   I+C=SᴴQS. It is positive definite. Apply the normalized trace-log
   formula and the resolvent trace formula, then the shift-kernel formula.
   The normalization SᴴPS=I is an explicit algebraic premise of this helper;
   the full proof must still construct such an invertible S for every P>0.
   It is not an assumed entropy or pencil-integral conclusion.

## Pinned reuse and remaining obligations

Mathlib pin: `0df444a360eaa60ab8c11dca51a86af692955474`.
Primary source APIs inspected locally:

- `Matrix.IsHermitian.det_eq_prod_eigenvalues`,
  `Matrix.PosDef.eigenvalues_pos`, and `Matrix.PosDef.det_pos`.
- `cfc_ringInverse_id`, `cfc_inv_id`, and finite-spectrum `cfc_comp'`.
- `Matrix.nonsing_inv_eq_ringInverse`, `Matrix.mul_inv_rev`,
  `Matrix.conjTranspose_nonsing_inv`, and inverse cancellation for units.
- `Matrix.PosDef.conjTranspose_mul_mul_same`,
  `Matrix.mulVec_injective_of_isUnit`, and cyclic trace.
- `Real.log_prod` and `Real.log_div` with their nonzero premises.

Existing accepted project statements to reuse without rewriting their
proofs: `spectral_function_semantics`, `c16_trR_cfc_product`,
`c16_trR_cfc_product_same`, `c11_cfc_identityShift`,
`c11_cfc_function_identityShift`, and `c11_log_identityShift`.

The plan contains no bodies and makes no compiler claim. The root-owned
inertia/dimension component is separate. Even after these helpers, the full
proof still needs the normalizer construction, the weighted pencil-count
integral, the justified product-integral exchange, and the exact hockey-stick
substitutions and finite cutoff. Full C11 remains unproved, and no original
target or completed Lean count increases.
