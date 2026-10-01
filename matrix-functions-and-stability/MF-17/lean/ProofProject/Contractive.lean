import ProofProject.Definitions

/-! # Dissipativity and the contractive endpoint -/

noncomputable section

namespace ProofProject

open Set
open scoped InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Contractive semigroup orbits have nonincreasing norm. -/
theorem contractive_orbit_norm_antitone (T : StableSemigroup 1 H) (x : H) :
    AntitoneOn (fun t : ℝ => ‖T.op t x‖) (Ici 0) := by
  intro s hs t ht hst
  have hd : 0 ≤ t - s := sub_nonneg.mpr hst
  have he : ‖T.op (t - s)‖ ≤ 1 := by
    calc
      ‖T.op (t - s)‖ ≤ 1 * Real.exp (-(t - s)) := T.bound _ hd
      _ ≤ 1 := by simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr hd)
  have hop : T.op t = (T.op (t - s)).comp (T.op s) := by
    simpa using T.add (t - s) s hd hs
  change ‖T.op t x‖ ≤ ‖T.op s x‖
  rw [hop, ContinuousLinearMap.comp_apply]
  calc
    ‖T.op (t - s) (T.op s x)‖ ≤ ‖T.op (t - s)‖ * ‖T.op s x‖ :=
      (T.op (t - s)).le_opNorm _
    _ ≤ 1 * ‖T.op s x‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
    _ = ‖T.op s x‖ := one_mul _

/-- The strong generator of a contractive semigroup is dissipative. -/
theorem generatorGraph_re_inner_nonpos (T : StableSemigroup 1 H) {x y : H}
    (hxy : GeneratorGraph T x y) : (inner ℂ y x).re ≤ 0 := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  have hd := hxy.norm_sq
  have hm : AntitoneOn (fun t : ℝ => ‖T.op t x‖ ^ 2) (Ici 0) := by
    intro s hs t ht hst
    exact pow_le_pow_left₀ (norm_nonneg _) (contractive_orbit_norm_antitone T x hs ht hst) 2
  have ha : AccPt (0 : ℝ) (Filter.principal (Ici 0)) :=
    uniqueDiffWithinAt_iff_accPt.mp (uniqueDiffWithinAt_Ici 0)
  have hh := hd.nonpos_of_antitoneOn ha hm
  simp only [T.at_zero, ContinuousLinearMap.id_apply, real_inner_eq_re_inner,
    RCLike.re_to_complex] at hh
  have hi : (inner ℂ x y).re = (inner ℂ y x).re := inner_re_symm (𝕜 := ℂ) _ _
  linarith

/-- A bounded inverse of the generator is itself dissipative. -/
theorem generatorInverse_re_inner_nonpos (T : StableSemigroup 1 H) (B : H →L[ℂ] H)
    (hB : IsGeneratorInverse T B) (x : H) : (inner ℂ (B x) x).re ≤ 0 := by
  have hg : GeneratorGraph T (B x) x := (hB _ _).mpr rfl
  have h := generatorGraph_re_inner_nonpos T hg
  calc
    (inner ℂ (B x) x).re = (inner ℂ x (B x)).re := inner_re_symm (𝕜 := ℂ) _ _
    _ ≤ 0 := h

variable [CompleteSpace H]

/-- The bounded exponential solves the differential equation with coefficient `B`. -/
theorem inverseEvolution_hasDerivAt (B : H →L[ℂ] H) (x : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => inverseEvolution B s x)
      (B (inverseEvolution B t x)) t := by
  have hd := hasDerivAt_exp_smul_const' B t
  have hv := ((ContinuousLinearMap.apply ℂ H x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd
  simpa [inverseEvolution, Complex.coe_smul, Function.comp_def, mul_apply_eq_comp] using hv

/-- The exponential of an everywhere defined dissipative operator is contractive. -/
theorem inverseEvolution_norm_le_one_of_dissipative (B : H →L[ℂ] H)
    (hB : ∀ x : H, (inner ℂ (B x) x).re ≤ 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖inverseEvolution B t‖ ≤ 1 := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have hd (s : ℝ) := (inverseEvolution_hasDerivAt B x s).norm_sq
  have hm : Antitone (fun s : ℝ => ‖inverseEvolution B s x‖ ^ 2) := by
    apply antitone_of_hasDerivAt_nonpos hd
    intro s
    change 2 * inner ℝ (inverseEvolution B s x) (B (inverseEvolution B s x)) ≤ 0
    have hi : inner ℝ (inverseEvolution B s x) (B (inverseEvolution B s x)) =
        (inner ℂ (B (inverseEvolution B s x)) (inverseEvolution B s x)).re := by
      exact inner_re_symm (𝕜 := ℂ) _ _
    rw [hi]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (hB _)
  have h := hm ht
  simp only [inverseEvolution, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero,
    one_apply_eq_self] at h
  simpa only [one_mul, inverseEvolution] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- The contractive case of the inverse-generator estimate. -/
theorem generatorInverse_evolution_norm_le_one (T : StableSemigroup 1 H)
    (B : H →L[ℂ] H) (hB : IsGeneratorInverse T B) {t : ℝ} (ht : 0 ≤ t) :
    ‖inverseEvolution B t‖ ≤ 1 :=
  inverseEvolution_norm_le_one_of_dissipative B (generatorInverse_re_inner_nonpos T B hB) ht

end ProofProject
