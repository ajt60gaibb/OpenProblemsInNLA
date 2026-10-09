import NLA.KE03.History
import NLA.KE03.Selection
import NLA.KE03.PowerEstimates
import NLA.KE03.Geometry
import NLA.KE03.Degree

/-! Every good seed succeeds for the actual, terminating query algorithm. -/

noncomputable section

namespace NLA.KE03

theorem goodSeed_successful {n : ℕ} (hn : 0 < n) (A V W : Mat n)
    (lam : Fin n → ℂ) (hVW : V * W = 1) (hWV : W * V = 1)
    (hA : A = V * Matrix.diagonal lam * W) {K ε : ℝ} (hK : 1 ≤ K)
    (hcond : opNorm V * opNorm W ≤ K) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hρ : 0 < radius A) (seed : Seed n) (hgood : GoodSeed W seed)
    {z : ℂ} {m : ℕ} (hz : (z, m) ∈ runAlgorithm n K ε (act A) seed) :
    Successful A ε z := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hrad := radius_eq_diagonal_norm hn A V W lam hVW hWV hA
  have hR : 0 < ‖lam‖ := hrad ▸ hρ
  obtain ⟨hm, hfinish⟩ := runAlgorithm_spec hz
  obtain ⟨hmpos, hFm⟩ := degreeSearch_spec hm
  have hF : 0 ≤ distortion n K := le_trans (by norm_num) (distortion_ge_one hn hK)
  have ha : 1 ≤ 1 + eta ε := by linarith [eta_pos hε]
  have hbase := shifted_power_bounds hn A V W lam hVW hWV hA K hK hcond seed hgood 0 m
  simp only [add_zero, zero_smul] at hbase
  have hnorm : normSq ((history (act A) (seedVector seed) m).headD 0) =
      ‖act (A ^ m) (seedVector seed)‖ ^ 2 := by
    rw [normSq_eq_norm_sq, history_head]
  have hS : normSq ((history (act A) (seedVector seed) m).headD 0) ≠ 0 := by
    rw [hnorm]
    intro hzero
    have hh : ‖act (A ^ m) (seedVector seed)‖ = 0 := by nlinarith
    have hb := hbase.1
    rw [hh, mul_zero] at hb
    exact (pow_pos hR m).not_ge hb
  obtain ⟨r, q, hr, hq, hzout⟩ := finish_spec hfinish hS
  obtain ⟨hrpos, hrlo, hrhi⟩ := radiusSearch_spec hr
  rw [hnorm] at hrlo hrhi
  obtain ⟨hlo, hup⟩ := radius_from_powers hmpos hF ha hR.le (norm_nonneg _)
    hrpos.le hFm hbase.1 hbase.2 hrlo hrhi
  obtain ⟨hqpos, hmesh⟩ := meshSearch_spec hq
  obtain ⟨iStar, hstar⟩ := (IsGreatest.pi_norm lam).1
  change ‖lam iStar‖ = ‖lam‖ at hstar
  have hdir : ‖lam iStar / (‖lam‖ : ℂ)‖ = 1 := by
    rw [norm_div, hstar, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    exact div_self hR.ne'
  obtain ⟨us, hus, hnet⟩ := circleMesh_near hqpos hε hmesh hdir
  let u := selectShift (history (act A) (seedVector seed) m) m q r
  have hsel := selectShift_max (history (act A) (seedVector seed) m) m q r hus
  rw [shiftedPower_history, shiftedPower_history] at hsel
  have hstarshift := shifted_power_bounds hn A V W lam hVW hWV hA K hK hcond
    seed hgood ((r : ℂ) * us) m
  have hbestshift := shifted_power_bounds hn A V W lam hVW hWV hA K hK hcond
    seed hgood ((r : ℂ) * u) m
  have hshift := shifted_radius_from_powers hmpos hF (by linarith : 0 ≤ 1 + eta ε)
    (norm_nonneg _) hFm hstarshift.1 hsel hbestshift.2
  obtain ⟨i, hi, hdist⟩ := location_from_shift_max hn lam rfl hR hrpos hε hεhalf
    (selectShift_unit _ _ _ _) (circleMesh_unit hus) hstar hnet hlo hup hshift
  refine ⟨lam i, (eigenvalue_iff_diagonal A V W lam hVW hWV hA _).mpr ⟨i, rfl⟩, ?_, ?_⟩
  · simpa only [hrad] using hi
  · simpa only [hzout, hrad] using hdist

theorem seedProbability_mono {n : ℕ} {p q : Seed n → Prop} (hpq : ∀ s, p s → q s) :
    seedProbability n p ≤ seedProbability n q := by
  classical
  have hc : Fintype.card {s : Seed n // p s} ≤ Fintype.card {s : Seed n // q s} := by
    apply Fintype.card_le_of_injective (fun s => ⟨s.val, hpq s.val s.property⟩)
    intro a b hab
    exact Subtype.ext (congrArg (fun s : {s : Seed n // q s} => s.val) hab)
  unfold seedProbability
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)

/-- The universal constant is explicit; this includes termination on every
seed, a realizable oracle trace, the query bound, and the joint success event. -/
theorem solvesKE03 : SolvesKE03 32768 := by
  intro n hn K ε hK hε hεhalf A hcond hρ
  obtain ⟨V, W, lam, hVW, hWV, hA, hcond⟩ := hcond
  refine ⟨fun seed => runAlgorithm_dom K hε (act A) seed, ?_, ?_⟩
  · intro seed z q hz
    exact ⟨history_trace _ _ _, degreeSearch_query_bound hn hK hε hεhalf
      (runAlgorithm_spec hz).1⟩
  · apply le_trans (goodSeed_probability hn W)
    apply seedProbability_mono
    intro seed hgood
    obtain ⟨⟨z, q⟩, hz⟩ := Part.dom_iff_mem.mp (runAlgorithm_dom K hε (act A) seed)
    exact ⟨z, q, hz, goodSeed_successful hn A V W lam hVW hWV hA hK hcond
      hε hεhalf hρ seed hgood hz⟩

end NLA.KE03
