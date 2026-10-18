import NLA.Proofs.PF05.PositiveCoercivity
import NLA.Proofs.PF05.CongruenceTransport
import Mathlib

/-! Closedness of the actual congruence orbit in the rank-three PSD
factorization fiber. Compactness is derived from the fixed positive definite
row aggregate and the actual convergent factor families. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.PF05.PositiveOrbitClosed
open Matrix Filter Topology
open NLA.Statements.PF05
open scoped BigOperators Matrix Matrix.Norms.Elementwise
abbrev Sym2 := Matrix (Fin 2) (Fin 2) ℝ
local instance : FirstCountableTopology Sym2 :=
  inferInstanceAs (FirstCountableTopology (Fin 2 → Fin 2 → ℝ))

/-- A bounded trace of actual congruences bounds every congruence matrix. -/
theorem norm_bounded_of_trace_bound (P : Sym2) (hP : P.PosDef)
    (C : ℝ) (hC : 0 ≤ C) (S : Sym2)
    (htrace : (S.transpose * P * S).trace ≤ C) :
    ‖S‖ ≤ C / (P.det / P.trace) + 1 := by
  have hd := PositiveCoercivity.det_div_trace_pos P hP
  have hquot : 0 ≤ C / (P.det / P.trace) := div_nonneg hC hd.le
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  rw [Real.norm_eq_abs, abs_le]
  have hsquare : (S i j) ^ 2 ≤ C / (P.det / P.trace) :=
    (le_div_iff₀ hd).mpr (by
      nlinarith [PositiveCoercivity.det_div_trace_entry_sq_lower P hP S i j])
  constructor <;> nlinarith [sq_nonneg (S i j - 1), sq_nonneg (S i j + 1)]

/-- A convergent family of actual congruence images has bounded congruence
matrices, without assuming a bounded choice of representatives. -/
theorem congruence_sequence_bounded (P : Sym2) (hP : P.PosDef)
    (S : ℕ → Sym2) (Q : Sym2)
    (hQ : Tendsto (fun n => (S n).transpose * P * S n) atTop (𝓝 Q)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ n, ‖S n‖ ≤ R := by
  have ht : Tendsto (fun n => ((S n).transpose * P * S n).trace) atTop (𝓝 Q.trace) :=
    (by fun_prop : Continuous (fun X : Sym2 => X.trace)).tendsto Q |>.comp hQ
  obtain ⟨C, hC, hbound⟩ :=
    (Metric.isBounded_range_of_tendsto _ ht).exists_pos_norm_le
  have hd := PositiveCoercivity.det_div_trace_pos P hP
  refine ⟨C / (P.det / P.trace) + 1, by positivity, ?_⟩
  intro n
  apply norm_bounded_of_trace_bound P hP C hC.le
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hbound _ ⟨n, rfl⟩)

/-- A limit inside the same rank-three factorization fiber of congruent
factorizations is again congruent. Invertibility is proved at the actual
limit; the dual family is recovered by nondegeneracy of the trace pairing. -/
theorem congruent_of_tendsto {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → Sym2) (B : Fin q → Sym2)
    (hfact : Factorization M A B) (hrank : M.rank = 3)
    (At : ℕ → Fin p → Sym2) (Bt : ℕ → Fin q → Sym2)
    (Al : Fin p → Sym2) (Bl : Fin q → Sym2)
    (halt : Factorization M Al Bl)
    (hAt : Tendsto At atTop (𝓝 Al))
    (_hBt : Tendsto Bt atTop (𝓝 Bl))
    (hc : ∀ n, Congruent A (At n) B (Bt n)) :
    Congruent A Al B Bl := by
  classical
  choose S hS hrows hcols using hc
  have hagg : Tendsto (fun n => ∑ i, At n i) atTop (𝓝 (∑ i, Al i)) :=
    tendsto_finsetSum _ (fun i _ => (tendsto_pi_nhds.mp hAt) i)
  have hQ : Tendsto (fun n => (S n).transpose * (∑ i, A i) * S n)
      atTop (𝓝 (∑ i, Al i)) := by
    convert hagg using 1
    funext n
    rw [← PositiveTopology.sum_congruence]
    apply Finset.sum_congr rfl
    intro i _
    exact (hrows n i).symm
  obtain ⟨R, hR, hbound⟩ := congruence_sequence_bounded (∑ i, A i)
    (PositiveTopology.sum_rows_posDef M A B hfact hrank) S (∑ i, Al i) hQ
  have hmem : ∀ n, S n ∈ Metric.closedBall (0 : Sym2) R := by
    intro n
    simpa only [Metric.mem_closedBall, dist_zero_right] using hbound n
  obtain ⟨Sl, _, φ, hmono, hlim⟩ :=
    (isCompact_closedBall (0 : Sym2) R).tendsto_subseq hmem
  have hrow : ∀ i, Al i = Sl.transpose * A i * Sl := by
    intro i
    have ha := ((tendsto_pi_nhds.mp hAt) i).comp hmono.tendsto_atTop
    have hs := ((by fun_prop : Continuous (fun X : Sym2 => X.transpose * A i * X)).tendsto Sl).comp hlim
    apply tendsto_nhds_unique ha
    exact hs.congr' (Eventually.of_forall (fun n => (hrows (φ n) i).symm))
  have hSl : Sl.det ≠ 0 :=
    PositiveTopology.congruence_det_nonzero_of_rank_three M A Al Bl hrank halt Sl hrow
  refine ⟨Sl, hSl, hrow, ?_⟩
  have hcong := factorization_congruence M A B hfact Sl hSl
  intro j
  have hzero : Bl j - dualCongruence Sl (B j) = 0 := by
    apply trace_pairing_left_nondegenerate_of_rank_three M Al Bl halt hrank
    · intro u v
      simp only [Matrix.sub_apply]
      rw [(halt.2.1 j).1 u v, dualCongruence_symmetric Sl (B j) (hfact.2.1 j).1 u v]
    · intro i
      rw [Matrix.mul_sub, Matrix.trace_sub]
      rw [← halt.2.2 i j]
      have hh := hcong.2.2 i j
      change M i j = (Sl.transpose * A i * Sl * dualCongruence Sl (B j)).trace at hh
      rw [← hrow i] at hh
      linarith
  exact sub_eq_zero.mp hzero

/-- The actual fiber, with its inherited finite-dimensional topology. -/
abbrev FactorizationFiber {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) :=
  {X : (Fin p → Sym2) × (Fin q → Sym2) // Factorization M X.1 X.2}

/-- Every actual congruence orbit is closed in the rank-three PSD
factorization fiber. This is a topological conclusion, with no assumed
closed-orbit or bounded-representative hypothesis. -/
theorem isClosed_congruence_orbit {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → Sym2) (B : Fin q → Sym2)
    (hfact : Factorization M A B) (hrank : M.rank = 3) :
    IsClosed {X : FactorizationFiber M | Congruent A X.val.1 B X.val.2} := by
  apply IsSeqClosed.isClosed
  intro X x hX hx
  apply congruent_of_tendsto M A B hfact hrank
      (fun n => (X n).val.1) (fun n => (X n).val.2) x.val.1 x.val.2 x.property
  · exact ((continuous_fst.comp continuous_subtype_val).tendsto x).comp hx
  · exact ((continuous_snd.comp continuous_subtype_val).tendsto x).comp hx
  · exact hX

#assert_trust kernel norm_bounded_of_trace_bound
#assert_trust kernel congruence_sequence_bounded
#assert_trust kernel congruent_of_tendsto
#assert_trust kernel isClosed_congruence_orbit
#print axioms congruence_sequence_bounded
#print axioms congruent_of_tendsto
#print axioms isClosed_congruence_orbit
end NLA.Proofs.PF05.PositiveOrbitClosed
