import NLA.Proofs.RA10.NuclearTraceDualAttains
import NLA.Proofs.RA10.NuclearNormTriangle
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic.NoncommRing

/-! RA-10: exact coefficient-one additivity of the frozen nuclear norm on
orthogonally supported complementary blocks. This is a partial dependency for
source Eq. (8), not the complete RA-10 Target. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped InnerProductSpace BigOperators

namespace NLA.Proofs.RA10

private theorem trace_toEuclideanLin_block {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (Matrix.toEuclideanLin A).trace ℝ (EuclideanSpace ℝ (Fin n)) =
      Matrix.trace A := by
  simpa only [Matrix.toEuclideanLin_eq_toLin_orthonormal] using
    Matrix.trace_toLin_eq A (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

private theorem trace_pairing_basis_block {n : ℕ}
    (W M : Matrix (Fin n) (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    Matrix.trace (W.transpose * M) =
      ∑ i : Fin n,
        ⟪Matrix.toEuclideanLin W (b i), Matrix.toEuclideanLin M (b i)⟫_ℝ := by
  let T := Matrix.toEuclideanLin M
  let V := Matrix.toEuclideanLin W
  have hmat : Matrix.toEuclideanLin (W.transpose * M) = V.adjoint ∘ₗ T := by
    rw [toEuclideanLin_mul_exact]
    have hT : Matrix.toEuclideanLin W.transpose = V.adjoint := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.toEuclideanLin_conjTranspose_eq_adjoint W
    rw [hT]
  calc
    Matrix.trace (W.transpose * M) =
        (Matrix.toEuclideanLin (W.transpose * M)).trace ℝ
          (EuclideanSpace ℝ (Fin n)) := (trace_toEuclideanLin_block _).symm
    _ = (V.adjoint ∘ₗ T).trace ℝ (EuclideanSpace ℝ (Fin n)) := by rw [hmat]
    _ = ∑ i : Fin n, ⟪b i, (V.adjoint ∘ₗ T) (b i)⟫_ℝ :=
      LinearMap.trace_eq_sum_inner _ b
    _ = ∑ i : Fin n, ⟪V (b i), T (b i)⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro i _
      simpa [LinearMap.comp_apply] using
        (V.adjoint_inner_right (b i) (T (b i)))

private theorem norm_map_gram_eigenvector_block {n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (i : Fin n) :
    ‖T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis (by simp) i)‖ =
      T.singularValues i.val := by
  let G := T.adjoint ∘ₗ T
  let hG := T.isSymmetric_adjoint_comp_self
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  let b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    hG.eigenvectorBasis hn
  have hunit : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
  have heig : G (b i) = hG.eigenvalues hn i • b i := by
    simp [G, b, hG.apply_eigenvectorBasis]
  have hsq : ‖T (b i)‖ ^ 2 = hG.eigenvalues hn i := by
    rw [← real_inner_self_eq_norm_sq]
    calc
      ⟪T (b i), T (b i)⟫_ℝ = ⟪b i, G (b i)⟫_ℝ := by
        simpa [G, LinearMap.comp_apply] using
          (T.adjoint_inner_right (b i) (T (b i))).symm
      _ = ⟪b i, (hG.eigenvalues hn i) • b i⟫_ℝ := by rw [heig]
      _ = hG.eigenvalues hn i := by
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hunit]
        ring
  have hsig := T.sq_singularValues_fin hn i
  have hnonneg := T.singularValues_nonneg i.val
  have hnorm : 0 ≤ ‖T (b i)‖ := norm_nonneg _
  have hmain : ‖T (b i)‖ = T.singularValues i.val := by nlinarith
  simpa [b, hG] using hmain

private theorem trace_contracting_le_nuclearNorm {n : ℕ}
    (W M : Matrix (Fin n) (Fin n) ℝ)
    (hW : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖Matrix.toEuclideanLin W x‖ ≤ ‖x‖) :
    Matrix.trace (W.transpose * M) ≤ NLA.Statements.RA10.NuclearNorm M := by
  let T := Matrix.toEuclideanLin M
  let V := Matrix.toEuclideanLin W
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  let b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn
  rw [trace_pairing_basis_block]
  unfold NLA.Statements.RA10.NuclearNorm
  apply Finset.sum_le_sum
  intro i _
  have hnormV : ‖V (b i)‖ ≤ 1 :=
    (hW (b i)).trans (b.orthonormal.norm_eq_one i).le
  have hnormT : ‖T (b i)‖ = T.singularValues i.val := by
    simpa [b, T] using norm_map_gram_eigenvector_block T i
  calc
    ⟪V (b i), T (b i)⟫_ℝ ≤ ‖V (b i)‖ * ‖T (b i)‖ :=
      real_inner_le_norm _ _
    _ ≤ T.singularValues i.val := by
      rw [hnormT]
      simpa using (mul_le_mul_of_nonneg_right hnormV
        (T.singularValues_nonneg i.val))

private theorem contraction_of_psd_gram {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ)
    (hW : Matrix.PosSemidef (1 - W.transpose * W)) :
    ∀ x : EuclideanSpace ℝ (Fin n),
      ‖Matrix.toEuclideanLin W x‖ ≤ ‖x‖ := by
  let V := Matrix.toEuclideanLin W
  have hpositive : (Matrix.toEuclideanLin (1 - W.transpose * W)).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr hW
  have hlinear : Matrix.toEuclideanLin (1 - W.transpose * W) =
      1 - V.adjoint ∘ₗ V := by
    rw [map_sub, toEuclideanLin_mul_exact]
    have htranspose : Matrix.toEuclideanLin W.transpose = V.adjoint := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.toEuclideanLin_conjTranspose_eq_adjoint W
    rw [htranspose]
    simp [V, Module.End.one_eq_id]
  intro x
  have hx := hpositive.inner_nonneg_right x
  rw [hlinear] at hx
  have hinner : ⟪x, V.adjoint (V x)⟫_ℝ = ‖V x‖ ^ 2 := by
    calc
      ⟪x, V.adjoint (V x)⟫_ℝ = ⟪V x, V x⟫_ℝ :=
        V.adjoint_inner_right x (V x)
      _ = ‖V x‖ ^ 2 := real_inner_self_eq_norm_sq (V x)
  have hsq : ‖V x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply,
      inner_sub_right, hinner] at hx
    have hx' : 0 ≤ ‖x‖ ^ 2 - ‖V x‖ ^ 2 := by
      simpa [Module.End.one_eq_id, real_inner_self_eq_norm_sq] using hx
    linarith
  have hnonnegV : 0 ≤ ‖V x‖ := norm_nonneg _
  have hnonnegX : 0 ≤ ‖x‖ := norm_nonneg _
  nlinarith

private theorem block_witness_contracts {n : ℕ}
    (P UX UY : Matrix (Fin n) (Fin n) ℝ)
    (hsym : P.transpose = P) (hid : P * P = P)
    (hUX : UX.transpose * UX = 1) (hUY : UY.transpose * UY = 1) :
    ∀ x : EuclideanSpace ℝ (Fin n),
      ‖Matrix.toEuclideanLin
        (P * UX * P + (1 - P) * UY * (1 - P)) x‖ ≤ ‖x‖ := by
  let Q : Matrix (Fin n) (Fin n) ℝ := 1 - P
  let W : Matrix (Fin n) (Fin n) ℝ := P * UX * P + Q * UY * Q
  have hQsym : Q.transpose = Q := by simp [Q, hsym]
  have hQid : Q * Q = Q := by
    dsimp [Q]
    noncomm_ring [hid]
  have hPQ : P * Q = 0 := by
    dsimp [Q]
    noncomm_ring [hid]
  have hQP : Q * P = 0 := by
    dsimp [Q]
    noncomm_ring [hid]
  have hsum : P + Q = 1 := by simp [Q]
  have hWtranspose : W.transpose =
      P * UX.transpose * P + Q * UY.transpose * Q := by
    dsimp [W]
    simp only [Matrix.transpose_add, Matrix.transpose_mul, hsym, hQsym]
    noncomm_ring
  have hcrossX :
      (P * UX.transpose * P) * (Q * UY * Q) = 0 := by
    calc
      (P * UX.transpose * P) * (Q * UY * Q) =
          P * UX.transpose * (P * Q) * UY * Q := by noncomm_ring
      _ = 0 := by rw [hPQ]; simp
  have hcrossY :
      (Q * UY.transpose * Q) * (P * UX * P) = 0 := by
    calc
      (Q * UY.transpose * Q) * (P * UX * P) =
          Q * UY.transpose * (Q * P) * UX * P := by noncomm_ring
      _ = 0 := by rw [hQP]; simp
  have hWtw : W.transpose * W =
      P * UX.transpose * P * UX * P +
      Q * UY.transpose * Q * UY * Q := by
    rw [hWtranspose]
    dsimp [W]
    calc
      (P * UX.transpose * P + Q * UY.transpose * Q) *
          (P * UX * P + Q * UY * Q) =
        (P * UX.transpose * P) * (P * UX * P) +
          (P * UX.transpose * P) * (Q * UY * Q) +
          (Q * UY.transpose * Q) * (P * UX * P) +
          (Q * UY.transpose * Q) * (Q * UY * Q) := by noncomm_ring
      _ = (P * UX.transpose * P) * (P * UX * P) +
          (Q * UY.transpose * Q) * (Q * UY * Q) := by
            rw [hcrossX, hcrossY]
            simp
      _ = P * UX.transpose * (P * P) * UX * P +
            Q * UY.transpose * (Q * Q) * UY * Q := by noncomm_ring
      _ = _ := by rw [hid, hQid]
  have hfirst : P - P * UX.transpose * P * UX * P =
      (Q * UX * P).transpose * (Q * UX * P) := by
    have hdecomp : P =
        P * UX.transpose * P * UX * P +
        P * UX.transpose * Q * UX * P := by
      calc
        P = P * (UX.transpose * UX) * P := by rw [hUX]; simp [hid]
        _ = P * UX.transpose * (P + Q) * UX * P := by rw [hsum]; noncomm_ring
        _ = P * UX.transpose * P * UX * P +
              P * UX.transpose * Q * UX * P := by noncomm_ring
    have hgramfirst :
        (Q * UX * P).transpose * (Q * UX * P) =
          P * UX.transpose * Q * UX * P := by
      simp only [Matrix.transpose_mul, hsym, hQsym]
      calc
        P * (UX.transpose * Q) * (Q * UX * P) =
            P * UX.transpose * (Q * Q) * UX * P := by noncomm_ring
        _ = P * UX.transpose * Q * UX * P := by rw [hQid]
    rw [hgramfirst]
    calc
      P - P * UX.transpose * P * UX * P =
          (P * UX.transpose * P * UX * P +
              P * UX.transpose * Q * UX * P) -
            P * UX.transpose * P * UX * P :=
        congrArg (fun Z : Matrix (Fin n) (Fin n) ℝ =>
          Z - P * UX.transpose * P * UX * P) hdecomp
      _ = P * UX.transpose * Q * UX * P := by abel
  have hsecond : Q - Q * UY.transpose * Q * UY * Q =
      (P * UY * Q).transpose * (P * UY * Q) := by
    have hdecomp : Q =
        Q * UY.transpose * Q * UY * Q +
        Q * UY.transpose * P * UY * Q := by
      calc
        Q = Q * (UY.transpose * UY) * Q := by rw [hUY]; simp [hQid]
        _ = Q * UY.transpose * (P + Q) * UY * Q := by rw [hsum]; noncomm_ring
        _ = Q * UY.transpose * Q * UY * Q +
              Q * UY.transpose * P * UY * Q := by noncomm_ring
    have hgramsecond :
        (P * UY * Q).transpose * (P * UY * Q) =
          Q * UY.transpose * P * UY * Q := by
      simp only [Matrix.transpose_mul, hsym, hQsym]
      calc
        Q * (UY.transpose * P) * (P * UY * Q) =
            Q * UY.transpose * (P * P) * UY * Q := by noncomm_ring
        _ = Q * UY.transpose * P * UY * Q := by rw [hid]
    rw [hgramsecond]
    calc
      Q - Q * UY.transpose * Q * UY * Q =
          (Q * UY.transpose * Q * UY * Q +
              Q * UY.transpose * P * UY * Q) -
            Q * UY.transpose * Q * UY * Q :=
        congrArg (fun Z : Matrix (Fin n) (Fin n) ℝ =>
          Z - Q * UY.transpose * Q * UY * Q) hdecomp
      _ = Q * UY.transpose * P * UY * Q := by abel
  have hgram : 1 - W.transpose * W =
      (Q * UX * P).transpose * (Q * UX * P) +
      (P * UY * Q).transpose * (P * UY * Q) := by
    rw [hWtw, ← hsum]
    calc
      P + Q - (P * UX.transpose * P * UX * P +
          Q * UY.transpose * Q * UY * Q) =
        (P - P * UX.transpose * P * UX * P) +
          (Q - Q * UY.transpose * Q * UY * Q) := by abel
      _ = _ := by rw [hfirst, hsecond]
  have hfirst : Matrix.PosSemidef
      ((Q * UX * P).transpose * (Q * UX * P)) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self (Q * UX * P)
  have hsecond : Matrix.PosSemidef
      ((P * UY * Q).transpose * (P * UY * Q)) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self (P * UY * Q)
  have hW : Matrix.PosSemidef (1 - W.transpose * W) := by
    rw [hgram]
    exact hfirst.add hsecond
  simpa [W, Q] using contraction_of_psd_gram W hW

theorem nuclearNorm_complementary_blocks_add {n : ℕ}
    (P X Y : Matrix (Fin n) (Fin n) ℝ)
    (hsym : P.transpose = P) (hid : P * P = P)
    (hX : P * X * P = X)
    (hY : (1 - P) * Y * (1 - P) = Y) :
    NLA.Statements.RA10.NuclearNorm (X + Y) =
      NLA.Statements.RA10.NuclearNorm X +
        NLA.Statements.RA10.NuclearNorm Y := by
  let Q : Matrix (Fin n) (Fin n) ℝ := 1 - P
  have hQsym : Q.transpose = Q := by simp [Q, hsym]
  have hQid : Q * Q = Q := by
    dsimp [Q]
    noncomm_ring [hid]
  have hPQ : P * Q = 0 := by
    dsimp [Q]
    noncomm_ring [hid]
  have hQP : Q * P = 0 := by
    dsimp [Q]
    noncomm_ring [hid]
  have hX' : P * X * P = X := hX
  have hY' : Q * Y * Q = Y := hY
  have hPX : P * X = X := by
    calc
      P * X = P * (P * X * P) := by rw [hX']
      _ = (P * P) * X * P := by noncomm_ring
      _ = X := by rw [hid, hX']
  have hXP : X * P = X := by
    calc
      X * P = (P * X * P) * P := by rw [hX']
      _ = P * X * (P * P) := by noncomm_ring
      _ = X := by rw [hid, hX']
  have hQY : Q * Y = Y := by
    calc
      Q * Y = Q * (Q * Y * Q) := by rw [hY']
      _ = (Q * Q) * Y * Q := by noncomm_ring
      _ = Y := by rw [hQid, hY']
  have hYQ : Y * Q = Y := by
    calc
      Y * Q = (Q * Y * Q) * Q := by rw [hY']
      _ = Q * Y * (Q * Q) := by noncomm_ring
      _ = Y := by rw [hQid, hY']
  have hQX : Q * X = 0 := by
    calc
      Q * X = Q * (P * X) := by rw [hPX]
      _ = (Q * P) * X := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hQP, zero_mul]
  have hPY : P * Y = 0 := by
    calc
      P * Y = P * (Q * Y) := by rw [hQY]
      _ = (P * Q) * Y := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hPQ, zero_mul]
  obtain ⟨UX, hUXleft, _hUXright, hUXtrace⟩ :=
    nuclearNorm_trace_orthogonal_attains X
  obtain ⟨UY, hUYleft, _hUYright, hUYtrace⟩ :=
    nuclearNorm_trace_orthogonal_attains Y
  let W : Matrix (Fin n) (Fin n) ℝ := P * UX * P + Q * UY * Q
  have hcontract : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖Matrix.toEuclideanLin W x‖ ≤ ‖x‖ := by
    simpa [W, Q] using
      block_witness_contracts P UX UY hsym hid hUXleft hUYleft
  have hWX : Matrix.trace (W.transpose * X) =
      Matrix.trace (UX.transpose * X) := by
    have hmat : W.transpose * X = P * UX.transpose * X := by
      dsimp [W]
      simp only [Matrix.transpose_add, Matrix.transpose_mul, hsym, hQsym, add_mul]
      noncomm_ring [hPX, hQX]
    rw [hmat]
    calc
      Matrix.trace (P * UX.transpose * X) =
          Matrix.trace (P * (UX.transpose * X)) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace ((UX.transpose * X) * P) :=
        Matrix.trace_mul_comm P (UX.transpose * X)
      _ = Matrix.trace (UX.transpose * X) := by rw [Matrix.mul_assoc, hXP]
  have hWY : Matrix.trace (W.transpose * Y) =
      Matrix.trace (UY.transpose * Y) := by
    have hmat : W.transpose * Y = Q * UY.transpose * Y := by
      dsimp [W]
      simp only [Matrix.transpose_add, Matrix.transpose_mul, hsym, hQsym, add_mul]
      noncomm_ring [hPY, hQY]
    rw [hmat]
    calc
      Matrix.trace (Q * UY.transpose * Y) =
          Matrix.trace (Q * (UY.transpose * Y)) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace ((UY.transpose * Y) * Q) :=
        Matrix.trace_mul_comm Q (UY.transpose * Y)
      _ = Matrix.trace (UY.transpose * Y) := by rw [Matrix.mul_assoc, hYQ]
  have htrace : Matrix.trace (W.transpose * (X + Y)) =
      NLA.Statements.RA10.NuclearNorm X +
        NLA.Statements.RA10.NuclearNorm Y := by
    rw [Matrix.mul_add, Matrix.trace_add, hWX, hWY, hUXtrace, hUYtrace]
  have hreverse := trace_contracting_le_nuclearNorm W (X + Y) hcontract
  rw [htrace] at hreverse
  exact le_antisymm (nuclearNorm_add_le X Y) hreverse

#assert_trust kernel trace_toEuclideanLin_block
#assert_trust kernel trace_pairing_basis_block
#assert_trust kernel norm_map_gram_eigenvector_block
#assert_trust kernel trace_contracting_le_nuclearNorm
#assert_trust kernel contraction_of_psd_gram
#assert_trust kernel block_witness_contracts
#assert_trust kernel nuclearNorm_complementary_blocks_add
#print axioms nuclearNorm_complementary_blocks_add

end NLA.Proofs.RA10
