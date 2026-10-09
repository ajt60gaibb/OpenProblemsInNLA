import ProofProject.AdjointSemigroup

/-!
# The bounded semigroup in the oscillatory reduction

For each positive evolution time `t`, the source uses
`u ↦ exp(u/t) T(u/t)`. These are actual bounded operators, with exact
semigroup bound `M` and strongly continuous adjoint orbits.
-/

noncomputable section

namespace ProofProject

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

namespace StableSemigroup

def oscillatoryRescale (T : StableSemigroup M H) (t u : ℝ) : H →L[ℂ] H :=
  (Real.exp (u / t) : ℂ) • T.op (u / t)

omit [CompleteSpace H] in
@[simp]
theorem oscillatoryRescale_zero (T : StableSemigroup M H) (t : ℝ) :
    T.oscillatoryRescale t 0 = ContinuousLinearMap.id ℂ H := by
  simp [oscillatoryRescale, T.at_zero]

omit [CompleteSpace H] in
theorem oscillatoryRescale_add (T : StableSemigroup M H) {t : ℝ} (ht : 0 < t)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    T.oscillatoryRescale t (u + v) =
      (T.oscillatoryRescale t u).comp (T.oscillatoryRescale t v) := by
  ext x
  simp only [oscillatoryRescale, smul_apply,
    ContinuousLinearMap.comp_apply, map_smul, add_div,
    T.add _ _ (div_nonneg hu ht.le) (div_nonneg hv ht.le), Real.exp_add,
    Complex.ofReal_mul, mul_smul]
  exact smul_comm _ _ _

theorem norm_oscillatoryRescale_le (T : StableSemigroup M H) {t u : ℝ}
    (ht : 0 < t) (hu : 0 ≤ u) : ‖T.oscillatoryRescale t u‖ ≤ M := by
  rw [oscillatoryRescale, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (u / t) * ‖T.op (u / t)‖ ≤
        Real.exp (u / t) * (M * Real.exp (-(u / t))) :=
      mul_le_mul_of_nonneg_left (T.bound _ (div_nonneg hu ht.le)) (Real.exp_pos _).le
    _ = M := by
      rw [mul_left_comm, ← Real.exp_add]
      simp

omit [CompleteSpace H] in
theorem oscillatoryRescale_strong_continuous (T : StableSemigroup M H)
    {t : ℝ} (ht : 0 < t) (x : H) :
    ContinuousOn (fun u : ℝ => T.oscillatoryRescale t u x) (Set.Ici 0) := by
  have he : Continuous (fun u : ℝ => (Real.exp (u / t) : ℂ)) := by fun_prop
  exact he.continuousOn.smul ((T.strong_continuous x).comp
    (continuous_id.div_const t).continuousOn (fun u hu => div_nonneg hu ht.le))

theorem oscillatoryRescale_adjoint_strong_continuous (T : StableSemigroup M H)
    {t : ℝ} (ht : 0 < t) (x : H) :
    ContinuousOn (fun u : ℝ => star (T.oscillatoryRescale t u) x) (Set.Ici 0) := by
  have he : Continuous (fun u : ℝ => (Real.exp (u / t) : ℂ)) := by fun_prop
  have h : ContinuousOn
      (fun u : ℝ => (Real.exp (u / t) : ℂ) • star (T.op (u / t)) x) (Set.Ici 0) :=
    he.continuousOn.smul ((T.adjoint_strong_continuous x).comp
      (continuous_id.div_const t).continuousOn (fun u hu => div_nonneg hu ht.le))
  simpa only [oscillatoryRescale, star_smul, Complex.star_def, Complex.conj_ofReal,
    smul_apply, Pi.smul_apply, Function.comp_apply, id_eq] using h

end StableSemigroup

end ProofProject
