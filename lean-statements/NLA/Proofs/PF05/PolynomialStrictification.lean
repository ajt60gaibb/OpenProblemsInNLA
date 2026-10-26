import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Tactic

/-! Actual finite signed-polynomial strictification by Lagrange interpolation.
Only the roots of the given nonzero weakly feasible polynomial need repair;
their number is bounded by its actual degree. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05
open Polynomial Filter Topology
noncomputable section

/-- At finitely many distinct real nodes, a nonzero weakly signed polynomial
can be replaced by an actual strictly signed nonzero polynomial of the same
degree bound. No cone dichotomy or interpolation oracle is assumed. -/
theorem polynomial_signed_strictification {ι : Type*} (s : Finset ι)
    (x sign : ι → ℝ) (hx : Set.InjOn x s)
    (hsign : ∀ i ∈ s, sign i ≠ 0) (p : ℝ[X]) (hp : p ≠ 0) (d : ℕ)
    (hdegree : p.natDegree ≤ d) (hweak : ∀ i ∈ s, 0 ≤ sign i * p.eval (x i)) :
    ∃ q : ℝ[X], q.natDegree ≤ d ∧ q ≠ 0 ∧ ∀ i ∈ s, 0 < sign i * q.eval (x i) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨p, hdegree, hp, by simp⟩
  let z := s.filter (fun i => p.eval (x i) = 0)
  have hzsub : z ⊆ s := Finset.filter_subset _ _
  have hzcard : z.card ≤ p.natDegree := by
    by_contra h
    apply hp
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
      (f := fun i : z => x i) (by
        intro i j hij
        exact Subtype.ext (hx (hzsub i.property) (hzsub j.property) hij))
    · intro i
      exact (Finset.mem_filter.mp i.property).2
    · simpa only [Fintype.card_coe] using Nat.lt_of_not_ge h
  let r := Lagrange.interpolate z x sign
  have hr : r.natDegree ≤ d := by
    have hrd := Lagrange.degree_interpolate_le sign (hx.mono hzsub)
    exact (Polynomial.natDegree_le_of_degree_le hrd).trans (by omega)
  have hroot (i : ι) (hi : i ∈ z) : r.eval (x i) = sign i :=
    Lagrange.eval_interpolate_at_node sign (hx.mono hzsub) hi
  have hev : ∀ᶠ ε : ℝ in 𝓝 0, ∀ i ∈ s, p.eval (x i) ≠ 0 →
      0 < sign i * (p.eval (x i) + ε * r.eval (x i)) := by
    apply (Filter.eventually_all_finset s).mpr
    intro i hi
    by_cases hz : p.eval (x i) = 0
    · exact Filter.Eventually.of_forall (fun _ hne => (hne hz).elim)
    · have hstrict : 0 < sign i * p.eval (x i) :=
        lt_of_le_of_ne (hweak i hi) (Ne.symm (mul_ne_zero (hsign i hi) hz))
      have hcont : Continuous (fun ε : ℝ => sign i * (p.eval (x i) + ε * r.eval (x i))) := by
        fun_prop
      have he : ∀ᶠ ε : ℝ in 𝓝 0,
          0 < sign i * (p.eval (x i) + ε * r.eval (x i)) :=
        hcont.continuousAt.eventually (eventually_gt_nhds (by simpa using hstrict))
      exact he.mono (fun _ h _ => h)
  obtain ⟨δ, hδ, hclose⟩ := Metric.eventually_nhds_iff.mp hev
  let ε := δ / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have heclose : dist ε 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]
    dsimp [ε]
    linarith
  let q := p + C ε * r
  have hqdegree : q.natDegree ≤ d := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le hdegree
    calc
      (C ε * r).natDegree ≤ (C ε).natDegree + r.natDegree := Polynomial.natDegree_mul_le
      _ = r.natDegree := by simp
      _ ≤ d := hr
  have hstrict (i : ι) (hi : i ∈ s) : 0 < sign i * q.eval (x i) := by
    by_cases hz : p.eval (x i) = 0
    · have hiz : i ∈ z := Finset.mem_filter.mpr ⟨hi, hz⟩
      have hi2 : 0 < sign i ^ 2 := sq_pos_of_ne_zero (hsign i hi)
      have hmul := mul_pos hε hi2
      simpa [q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        hz, hroot i hiz, pow_two, mul_assoc, mul_comm, mul_left_comm] using hmul
    · simpa [q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] using
        hclose heclose i hi hz
  have hq : q ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := hs
    have h := hstrict i hi
    simp [hz] at h
  exact ⟨q, hqdegree, hq, hstrict⟩

#assert_trust kernel polynomial_signed_strictification
#print axioms polynomial_signed_strictification
end
end NLA.Proofs.PF05
