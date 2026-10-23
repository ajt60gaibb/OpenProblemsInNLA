import NLA.Proofs.PF05.ContactQuartic

/-! Strict determinant normals give actual common straight PSD segments. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05
open NLA.Statements.PF05 CoordinateActions Filter Topology
noncomputable section

/-- Positive determinant derivative at each singular nonzero PSD factor is
sufficient for actual straight feasibility, including time zero. -/
theorem eventually_psd_line_of_strict (A E : M2) (hA : PositiveSemidefinite A)
    (hne : A ≠ 0) (hE : Symmetric E)
    (hstrict : A.det = 0 → 0 < determinantDirection A E) :
    ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ t → PositiveSemidefinite (A+t • E) := by
  have htrace : 0 < A.trace := by
    have hn := ((psd_iff_posSemidef A).mp hA).trace_nonneg
    exact lt_of_le_of_ne hn (fun h => hne (psd_zero_of_trace_zero A hA h.symm))
  have htcont : Continuous (fun t : ℝ => (A+t • E).trace) := by
    simp only [Matrix.trace_fin_two, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  have hevtrace : ∀ᶠ t : ℝ in 𝓝 0, 0 < (A+t • E).trace :=
    htcont.continuousAt.eventually (eventually_gt_nhds (by simpa using htrace))
  have hevdet : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ t → 0 ≤ (A+t • E).det := by
    by_cases hz : A.det = 0
    · have hc : Continuous (fun t : ℝ => determinantDirection A E + t*E.det) := by fun_prop
      have he : ∀ᶠ t : ℝ in 𝓝 0, 0 < determinantDirection A E + t*E.det :=
        hc.continuousAt.eventually (eventually_gt_nhds (by simpa using hstrict hz))
      filter_upwards [he] with t ht htn
      rw [det_add_smul_two A E hA.1 hE, hz]
      have hh := mul_nonneg htn ht.le
      nlinarith
    · have hd : 0 < A.det := lt_of_le_of_ne (psd_det_nonneg A hA) (Ne.symm hz)
      have hc : Continuous (fun t : ℝ => (A+t • E).det) := by
        simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        fun_prop
      have he : ∀ᶠ t : ℝ in 𝓝 0, 0 < (A+t • E).det :=
        hc.continuousAt.eventually (eventually_gt_nhds (by simpa using hd))
      exact he.mono (fun _ h _ => h.le)
  filter_upwards [hevtrace, hevdet] with t ht hd htn
  apply psd_two_of_trace_pos_det_nonneg _ _ ht (hd htn)
  intro i j
  simp [Matrix.add_apply, Matrix.smul_apply, hA.1 i j, hE i j]

/-- Actual coordinate actions with strictly inward determinant normals form
an actual frozen feasible direction, with a single interval for both families. -/
theorem strict_actions_feasible {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → M2) (B : Fin q → M2) (hfact : Factorization M A B)
    (ha : ∀ i, A i ≠ 0) (hb : ∀ j, B j ≠ 0) (T : M3)
    (hprimal : ∀ i, (A i).det = 0 → 0 < determinantDirection (A i) (primal T (A i)))
    (hdual : ∀ j, (B j).det = 0 → 0 < determinantDirection (B j) (-dual T (B j))) :
    FeasibleDirection A (fun i => primal T (A i)) B (fun j => -dual T (B j)) := by
  refine ⟨fun i => primal_symmetric _ _, ?_, ?_, ?_⟩
  · intro j a b
    simp [dual_symmetric T (B j) a b]
  · intro i j
    exact coordinateActions_trace_cancel T (A i) (B j) (hfact.1 i).1 (hfact.2.1 j).1
  · have heva : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 ≤ t →
        PositiveSemidefinite (A i+t • primal T (A i)) :=
      Filter.eventually_all.mpr (fun i => eventually_psd_line_of_strict _ _
        (hfact.1 i) (ha i) (primal_symmetric _ _) (hprimal i))
    have hevb : ∀ᶠ t : ℝ in 𝓝 0, ∀ j, 0 ≤ t →
        PositiveSemidefinite (B j+t • (-dual T (B j))) := by
      apply Filter.eventually_all.mpr
      intro j
      apply eventually_psd_line_of_strict _ _ (hfact.2.1 j) (hb j) _ (hdual j)
      intro a b
      simp [dual_symmetric T (B j) a b]
    obtain ⟨δ, hδ, hclose⟩ := Metric.eventually_nhds_iff.mp (heva.and hevb)
    refine ⟨δ, hδ, fun t ht htd => ?_⟩
    have hd : dist t 0 < δ := by simpa [Real.dist_eq, abs_of_nonneg ht] using htd
    exact ⟨fun i => (hclose hd).1 i ht, fun j => (hclose hd).2 j ht⟩

/-- A common scalar primal action on an actual full-rank factorization has
zero contact polynomial. This uses the actual row span, rather than an
extra injectivity hypothesis on the coordinate map. -/
theorem directionPolynomial_zero_of_scalar {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → M2) (B : Fin q → M2)
    (hfact : Factorization M A B) (hrank : M.rank = 3) (T : M3) (d : ℝ)
    (hscalar : ∀ i, primal T (A i) = d • A i) : directionPolynomial T = 0 := by
  obtain ⟨U, hUX⟩ := left_inverse_of_row_span (leftCoordinates A)
    (factorization_coordinate_spans M A B hfact hrank).1
  have hXT : leftCoordinates A * T = d • leftCoordinates A := by
    rw [← family_left_primal]
    ext i j
    change leftVector (primal T (A i)) j = d * leftVector (A i) j
    rw [hscalar i, leftVector_smul]
    rfl
  have hT : T = d • (1 : M3) := by
    calc
      T = U * (leftCoordinates A * T) := by rw [← Matrix.mul_assoc, hUX]; simp
      _ = U * (d • leftCoordinates A) := by rw [hXT]
      _ = d • (1 : M3) := by rw [Matrix.mul_smul, hUX]
  rw [hT]
  have hdd : d+d-2*d=0 := by ring
  simp [directionPolynomial, hdd]

#assert_trust kernel eventually_psd_line_of_strict
#assert_trust kernel strict_actions_feasible
#assert_trust kernel directionPolynomial_zero_of_scalar
#print axioms strict_actions_feasible
#print axioms directionPolynomial_zero_of_scalar
end
end NLA.Proofs.PF05
