import ProofProject.Definitions

/-! Diagonal operators in an arbitrary finite basis, with its given norm. -/

noncomputable section

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [FiniteDimensional ℂ H] {N : ℕ}

/-- The diagonal map in a possibly nonorthogonal basis. -/
def basisDiagonal (b : Module.Basis (Fin N) ℂ H) (a : Fin N → ℂ) : H →L[ℂ] H :=
  (b.constr ℂ (fun i => a i • b i)).toContinuousLinearMap

@[simp] theorem basisDiagonal_basis (b : Module.Basis (Fin N) ℂ H)
    (a : Fin N → ℂ) (i : Fin N) : basisDiagonal b a (b i) = a i • b i := by
  exact b.constr_basis ℂ _ i

omit [FiniteDimensional ℂ H] in
lemma basisCLM_ext (b : Module.Basis (Fin N) ℂ H) {S T : H →L[ℂ] H}
    (h : ∀ i, S (b i) = T (b i)) : S = T := by
  have hh : S.toLinearMap = T.toLinearMap := b.ext h
  ext x
  exact congrArg (fun L : H →ₗ[ℂ] H => L x) hh

@[simp] lemma basisDiagonal_zero (b : Module.Basis (Fin N) ℂ H) : basisDiagonal b 0 = 0 := by
  apply basisCLM_ext b
  intro i
  simp

@[simp] lemma basisDiagonal_one (b : Module.Basis (Fin N) ℂ H) : basisDiagonal b 1 = 1 := by
  apply basisCLM_ext b
  intro i
  simp

lemma basisDiagonal_add (b : Module.Basis (Fin N) ℂ H) (a d : Fin N → ℂ) :
    basisDiagonal b (a + d) = basisDiagonal b a + basisDiagonal b d := by
  apply basisCLM_ext b
  intro i
  simp [add_smul]

lemma basisDiagonal_smul (b : Module.Basis (Fin N) ℂ H) (z : ℂ) (a : Fin N → ℂ) :
    basisDiagonal b (z • a) = z • basisDiagonal b a := by
  apply basisCLM_ext b
  intro i
  simp [smul_smul]

lemma basisDiagonal_mul (b : Module.Basis (Fin N) ℂ H) (a d : Fin N → ℂ) :
    basisDiagonal b (a * d) = basisDiagonal b a * basisDiagonal b d := by
  apply basisCLM_ext b
  intro i
  simp [mul_apply_eq_comp, smul_smul, mul_comm]

/-- Diagonal functional calculus as a finite-dimensional algebra homomorphism. -/
def basisDiagonalAlgHom (b : Module.Basis (Fin N) ℂ H) :
    (Fin N → ℂ) →ₐ[ℂ] (H →L[ℂ] H) where
  toFun := basisDiagonal b
  map_zero' := basisDiagonal_zero b
  map_one' := basisDiagonal_one b
  map_add' := basisDiagonal_add b
  map_mul' := basisDiagonal_mul b
  commutes' z := by
    apply basisCLM_ext b
    intro i
    simp [Algebra.algebraMap_eq_smul_one]

lemma continuous_basisDiagonal (b : Module.Basis (Fin N) ℂ H) :
    Continuous (basisDiagonal b) :=
  (basisDiagonalAlgHom b).toLinearMap.continuous_of_finiteDimensional

lemma basisDiagonal_exp (b : Module.Basis (Fin N) ℂ H) (a : Fin N → ℂ) :
    NormedSpace.exp (basisDiagonal b a) = basisDiagonal b (fun i => Complex.exp (a i)) := by
  have h := NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) (basisDiagonalAlgHom b)
    (continuous_basisDiagonal b) a (by simp [NormedSpace.expSeries_radius_eq_top])
  change basisDiagonal b (NormedSpace.exp a) = NormedSpace.exp (basisDiagonal b a) at h
  rw [← h]
  congr 1
  funext i
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]

/-- A coordinate projection measured in the same norm as the diagonal map. -/
def basisCoordinate (b : Module.Basis (Fin N) ℂ H) (i : Fin N) : H →L[ℂ] H :=
  (b.coord i).toContinuousLinearMap.smulRight (b i)

@[simp] lemma basisCoordinate_apply (b : Module.Basis (Fin N) ℂ H) (i : Fin N) (x : H) :
    basisCoordinate b i x = b.repr x i • b i := rfl

lemma basisDiagonal_eq_sum (b : Module.Basis (Fin N) ℂ H) (a : Fin N → ℂ) :
    basisDiagonal b a = ∑ i, a i • basisCoordinate b i := by
  apply basisCLM_ext b
  intro j
  simp [basisCoordinate_apply, Module.Basis.repr_self, Finsupp.single_apply]

lemma basisDiagonal_apply (b : Module.Basis (Fin N) ℂ H) (a : Fin N → ℂ) (x : H) :
    basisDiagonal b a x = ∑ i, (a i * b.repr x i) • b i := by
  simp [basisDiagonal_eq_sum, basisCoordinate_apply, smul_smul]

@[simp] lemma basisDiagonal_repr (b : Module.Basis (Fin N) ℂ H)
    (a : Fin N → ℂ) (x : H) (i : Fin N) :
    b.repr (basisDiagonal b a x) i = a i * b.repr x i := by
  rw [basisDiagonal_apply]
  simp [Module.Basis.repr_self, Finsupp.single_apply]

lemma basisDiagonal_sub (b : Module.Basis (Fin N) ℂ H) (a d : Fin N → ℂ) :
    basisDiagonal b (a - d) = basisDiagonal b a - basisDiagonal b d :=
  (basisDiagonalAlgHom b).map_sub a d

/-- The ℓ¹ coefficient estimate retains explicit projection constants. -/
lemma norm_basisDiagonal_le (b : Module.Basis (Fin N) ℂ H) (a : Fin N → ℂ)
    {K : ℝ} (hK : ∀ i, ‖basisCoordinate b i‖ ≤ K) :
    ‖basisDiagonal b a‖ ≤ K * ∑ i, ‖a i‖ := by
  rw [basisDiagonal_eq_sum]
  calc
    ‖∑ i, a i • basisCoordinate b i‖ ≤ ∑ i, ‖a i • basisCoordinate b i‖ := norm_sum_le _ _
    _ ≤ ∑ i, K * ‖a i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, mul_comm K]
      exact mul_le_mul_of_nonneg_left (hK i) (norm_nonneg _)
    _ = K * ∑ i, ‖a i‖ := (Finset.mul_sum _ _ _).symm

/-- Entrywise errors are summed against coordinate-projection norms. -/
lemma norm_basisDiagonal_sub_le (b : Module.Basis (Fin N) ℂ H) (a d : Fin N → ℂ)
    {K : ℝ} (hK : ∀ i, ‖basisCoordinate b i‖ ≤ K) :
    ‖basisDiagonal b a - basisDiagonal b d‖ ≤ K * ∑ i, ‖a i - d i‖ := by
  rw [← basisDiagonal_sub]
  exact norm_basisDiagonal_le b (a - d) hK

end ProofProject
