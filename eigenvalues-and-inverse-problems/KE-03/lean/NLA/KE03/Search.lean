import NLA.KE03.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace NLA.KE03

theorem searchNat_spec {p : ℕ → Prop} {k : ℕ} (hk : k ∈ searchNat p) : p k := by
  classical
  rcases hk with ⟨h, rfl⟩
  exact Nat.find_spec h

theorem searchNat_min {p : ℕ → Prop} {k : ℕ} (hk : k ∈ searchNat p)
    {j : ℕ} (hj : j < k) : ¬p j := by
  classical
  rcases hk with ⟨h, rfl⟩
  exact Nat.find_min h hj

theorem eta_pos {ε : ℝ} (hε : 0 < ε) : 0 < eta ε := by
  unfold eta
  positivity

theorem degreeSearch_dom (n : ℕ) (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (degreeSearch n K ε).Dom := by
  change ∃ k, distortion n K ≤ (1 + eta ε) ^ (k + 1)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (distortion n K)
    (show (1 : ℝ) < 1 + eta ε by linarith [eta_pos hε])
  refine ⟨k, hk.le.trans ?_⟩
  exact pow_le_pow_right₀ (by linarith [eta_pos hε]) (Nat.le_succ k)

theorem degreeSearch_spec {n m : ℕ} {K ε : ℝ} (hm : m ∈ degreeSearch n K ε) :
    0 < m ∧ distortion n K ≤ (1 + eta ε) ^ m := by
  rcases (Part.mem_map_iff _).mp hm with ⟨k, hk, rfl⟩
  exact ⟨Nat.succ_pos _, searchNat_spec hk⟩

theorem positiveRational_pos (k : ℕ) : 0 < positiveRational k := by
  unfold positiveRational
  positivity

theorem positiveRational_surjective {r : ℚ} (hr : 0 < r) :
    ∃ k, positiveRational k = (r : ℝ) := by
  have hn : 0 < r.num := Rat.num_pos.mpr hr
  have hnat : 0 < r.num.toNat := by omega
  refine ⟨Nat.pair (r.num.toNat - 1) (r.den - 1), ?_⟩
  simp only [positiveRational, Nat.unpair_pair]
  rw [Nat.cast_sub (show 1 ≤ r.num.toNat by omega),
    Nat.cast_sub (show 1 ≤ r.den from r.pos), Nat.cast_one,
    sub_add_cancel, sub_add_cancel, Rat.cast_def]
  congr 1
  exact_mod_cast Int.toNat_of_nonneg hn.le

theorem radiusSearch_dom {m : ℕ} (hm : 0 < m) {ε S : ℝ}
    (hε : 0 < ε) (hS : 0 < S) : (radiusSearch m ε S).Dom := by
  let x : ℝ := S ^ ((2 * m : ℕ) : ℝ)⁻¹
  have hx : 0 < x := Real.rpow_pos_of_pos hS _
  have hxpow : x ^ (2 * m) = S :=
    Real.rpow_inv_natCast_pow hS.le (by omega)
  have ha : 1 < 1 + eta ε := by linarith [eta_pos hε]
  have hax : x / (1 + eta ε) < x := (div_lt_self hx ha)
  obtain ⟨r, hrlo, hrhi⟩ := exists_rat_btwn hax
  have hrpos : (0 : ℝ) < r := (div_pos hx (by linarith)).trans hrlo
  obtain ⟨k, hk⟩ := positiveRational_surjective (Rat.cast_pos.mp hrpos)
  change ∃ k, _
  refine ⟨k, ?_, ?_⟩
  · rw [hk, ← hxpow]
    exact pow_le_pow_left₀ hrpos.le hrhi.le _
  · rw [hk, ← hxpow]
    apply pow_le_pow_left₀ hx.le
    have := (div_lt_iff₀ (show 0 < 1 + eta ε by linarith)).mp hrlo
    nlinarith

theorem radiusSearch_spec {m : ℕ} {ε S r : ℝ} (hr : r ∈ radiusSearch m ε S) :
    0 < r ∧ r ^ (2 * m) ≤ S ∧ S ≤ ((1 + eta ε) * r) ^ (2 * m) := by
  rcases (Part.mem_map_iff _).mp hr with ⟨k, hk, rfl⟩
  exact ⟨positiveRational_pos k, searchNat_spec hk⟩

theorem meshSearch_dom {ε : ℝ} (hε : 0 < ε) : (meshSearch ε).Dom := by
  obtain ⟨k, hk⟩ := exists_nat_gt (32 / ε)
  change ∃ k : ℕ, (32 : ℝ) ≤ ε * (k + 1)
  refine ⟨k, ?_⟩
  have h := (div_lt_iff₀ hε).mp hk
  nlinarith

theorem meshSearch_spec {ε : ℝ} {q : ℕ} (hq : q ∈ meshSearch ε) :
    0 < q ∧ 32 ≤ ε * q := by
  rcases (Part.mem_map_iff _).mp hq with ⟨k, hk, rfl⟩
  exact ⟨Nat.succ_pos _, by simpa only [Nat.cast_add, Nat.cast_one] using searchNat_spec hk⟩

theorem normSq_eq_norm_sq {n : ℕ} (v : Vec n) : normSq v = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem normSq_nonneg {n : ℕ} (v : Vec n) : 0 ≤ normSq v := by
  rw [normSq_eq_norm_sq]
  positivity

theorem finish_dom {n m : ℕ} (h : List (Vec n)) (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    (finish h m ε).Dom := by
  classical
  unfold finish
  split_ifs with hz
  · trivial
  · have hS : 0 < normSq (h.headD 0) :=
      lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hz)
    apply Part.dom_iff_mem.mpr
    obtain ⟨r, hr⟩ := Part.dom_iff_mem.mp (radiusSearch_dom hm hε hS)
    obtain ⟨q, hq⟩ := Part.dom_iff_mem.mp (meshSearch_dom hε)
    exact ⟨_, Part.mem_bind hr (Part.mem_bind hq (Part.mem_some _))⟩

theorem history_trace {n : ℕ} (oracle : Vec n → Vec n) (b : Vec n) (m : ℕ) :
    QueryTrace oracle b (history oracle b m) m := by
  induction m with
  | zero => exact QueryTrace.initial
  | succ m ih => exact QueryTrace.query ih

theorem runAlgorithm_dom {n : ℕ} (K : ℝ) {ε : ℝ} (hε : 0 < ε)
    (oracle : Vec n → Vec n) (seed : Seed n) :
    (runAlgorithm n K ε oracle seed).Dom := by
  obtain ⟨m, hm⟩ := Part.dom_iff_mem.mp (degreeSearch_dom n K hε)
  obtain ⟨z, hz⟩ := Part.dom_iff_mem.mp
    (finish_dom (history oracle (seedVector seed) m) (degreeSearch_spec hm).1 hε)
  apply Part.dom_iff_mem.mpr
  exact ⟨(z, m), Part.mem_bind hm (Part.mem_bind hz (Part.mem_some _))⟩

theorem runAlgorithm_spec {n q : ℕ} {K ε : ℝ} {oracle : Vec n → Vec n}
    {seed : Seed n} {z : ℂ} (hz : (z, q) ∈ runAlgorithm n K ε oracle seed) :
    q ∈ degreeSearch n K ε ∧ z ∈ finish (history oracle (seedVector seed) q) q ε := by
  rcases Part.mem_bind_iff.mp hz with ⟨m, hm, hmz⟩
  rcases Part.mem_bind_iff.mp hmz with ⟨w, hw, hwm⟩
  have heq : (z, q) = (w, m) := Part.mem_some_iff.mp hwm
  cases heq
  exact ⟨hm, hw⟩

end NLA.KE03
