import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Cutting out the critical interval of an increasing phase derivative

A positive lower bound on the derivative controls the length between the
clipped levels `-μ` and `μ`. The two exterior intervals stay uniformly away
from zero. Degenerate intervals and functions entirely outside the critical
zone are included.
-/

noncomputable section

open Set

namespace ProofProject

/-- A lower bound on the derivative gives a quantitative increase between any
two points of the closed interval. -/
theorem mul_sub_le_sub_of_deriv_lower {a b κ : ℝ} {p p' : ℝ → ℝ}
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (p' x) x)
    (hlower : ∀ x ∈ Icc a b, κ ≤ p' x)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    κ * (y - x) ≤ p y - p x := by
  apply (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
    (fun u hu => (hp u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hp u (interior_subset hu)).differentiableAt.differentiableWithinAt)
    (fun u hu => ?_) x hx y hy hxy
  rw [(hp u (interior_subset hu)).deriv]
  exact hlower u (interior_subset hu)

/-- Cut out an interval of length at most `2μ/κ`; every nonempty exterior
piece has `|p| ≥ μ`. No continuity of the derivative is needed. -/
theorem exists_oscillatory_critical_interval {a b κ μ : ℝ}
    (hab : a ≤ b) (hκ : 0 < κ) (hμ : 0 < μ) {p p' : ℝ → ℝ}
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (p' x) x)
    (hlower : ∀ x ∈ Icc a b, κ ≤ p' x) :
    ∃ c d : ℝ, a ≤ c ∧ c ≤ d ∧ d ≤ b ∧ d - c ≤ 2 * μ / κ ∧
      (a < c → ∀ x ∈ Icc a c, μ ≤ |p x|) ∧
      (d < b → ∀ x ∈ Icc d b, μ ≤ |p x|) := by
  have hc : ContinuousOn p (Icc a b) :=
    fun x hx => (hp x hx).continuousAt.continuousWithinAt
  have hg {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
      κ * (y - x) ≤ p y - p x :=
    mul_sub_le_sub_of_deriv_lower hp hlower hx hy hxy
  have hm : MonotoneOn p (Icc a b) := by
    intro x hx y hy hxy
    have hprod := mul_nonneg hκ.le (sub_nonneg.mpr hxy)
    have hgxy := hg hx hy hxy
    linarith
  have hlength0 : (0 : ℝ) ≤ 2 * μ / κ := by positivity
  by_cases ha : μ ≤ p a
  · refine ⟨a, a, le_rfl, le_rfl, hab, ?_, ?_, ?_⟩
    · simpa only [sub_self] using hlength0
    · intro h
      exact (lt_irrefl a h).elim
    · intro _ x hx
      exact (ha.trans (hm ⟨le_rfl, hab⟩ hx hx.1)).trans (le_abs_self _)
  by_cases hb : p b ≤ -μ
  · refine ⟨b, b, hab, le_rfl, le_rfl, ?_, ?_, ?_⟩
    · simpa only [sub_self] using hlength0
    · intro _ x hx
      have hpx := (hm hx ⟨hab, le_rfl⟩ hx.2).trans hb
      exact (show μ ≤ -p x by linarith).trans (neg_le_abs _)
    · intro h
      exact (lt_irrefl b h).elim
  have hpa : p a < μ := lt_of_not_ge ha
  have hpb : -μ < p b := lt_of_not_ge hb
  have hex_c : ∃ c ∈ Icc a b, -μ ≤ p c ∧ (a < c → p c = -μ) := by
    by_cases h : p a ≤ -μ
    · obtain ⟨c, hcmem, hcp⟩ := intermediate_value_Icc hab hc ⟨h, hpb.le⟩
      exact ⟨c, hcmem, hcp.ge, fun _ => hcp⟩
    · refine ⟨a, ⟨le_rfl, hab⟩, (lt_of_not_ge h).le, ?_⟩
      intro hlt
      exact (lt_irrefl a hlt).elim
  have hex_d : ∃ d ∈ Icc a b, p d ≤ μ ∧ (d < b → p d = μ) := by
    by_cases h : μ ≤ p b
    · obtain ⟨d, hdmem, hdp⟩ := intermediate_value_Icc hab hc ⟨hpa.le, h⟩
      exact ⟨d, hdmem, hdp.le, fun _ => hdp⟩
    · refine ⟨b, ⟨hab, le_rfl⟩, (lt_of_not_ge h).le, ?_⟩
      intro hlt
      exact (lt_irrefl b hlt).elim
  obtain ⟨c, hcmem, hc_lower, hc_eq⟩ := hex_c
  obtain ⟨d, hdmem, hd_upper, hd_eq⟩ := hex_d
  have hcd : c ≤ d := by
    by_contra h
    have hdc : d < c := lt_of_not_ge h
    have hpc := hc_eq (lt_of_le_of_lt hdmem.1 hdc)
    have hpd := hd_eq (lt_of_lt_of_le hdc hcmem.2)
    have hord := hm hdmem hcmem hdc.le
    rw [hpc, hpd] at hord
    linarith
  refine ⟨c, d, hcmem.1, hcd, hdmem.2, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hκ).mpr
    have hgr := hg hcmem hdmem hcd
    nlinarith
  · intro hac x hx
    have hxmem : x ∈ Icc a b := ⟨hx.1, hx.2.trans hcmem.2⟩
    have hpx := hm hxmem hcmem hx.2
    rw [hc_eq hac] at hpx
    exact (show μ ≤ -p x by linarith).trans (neg_le_abs _)
  · intro hdb x hx
    have hxmem : x ∈ Icc a b := ⟨hdmem.1.trans hx.1, hx.2⟩
    have hpx := hm hdmem hxmem hx.1
    rw [hd_eq hdb] at hpx
    exact hpx.trans (le_abs_self _)

end ProofProject
