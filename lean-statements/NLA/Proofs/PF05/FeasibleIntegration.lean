import NLA.Proofs.PF05.InfinitesimalActions
import NLA.Proofs.PF05.PSDResolvent
import NLA.Proofs.PF05.OperatorFactorization

/-! Unrestricted actual integration of a feasible straight direction. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05
open NLA.Statements.PF05 CoordinateActions

/-- Every actual feasible direction integrates on a common interval to exact
PSD factorizations through its unique coordinate operator. This covers zero,
rank-one flat and strictly outward factors without a positivity assumption. -/
theorem integrate_feasible_direction {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A E : Fin p → M2) (B F : Fin q → M2)
    (hfact : Factorization M A B) (hrank : M.rank=3)
    (hdir : FeasibleDirection A E B F) :
    ∃ T : M3, ∃ h : ℝ, 0<h ∧
      (∀ i, E i=primal T (A i)) ∧ (∀ j, F j= -dual T (B j)) ∧
      ∀ t : ℝ, 0≤t → t<h →
        (1+t • T).det≠0 ∧
        Factorization M (fun i => A i+t • E i)
          (fun j => dual (inversePencil T t) (B j)) := by
  obtain ⟨T,hE,hF⟩ := feasible_direction_actions M A E B F hfact hrank hdir
  obtain ⟨a,ha,hsegment⟩ := hdir.2.2.2
  have hdual (j : Fin q) : ∃ h : ℝ, 0<h ∧ ∀ t, 0≤t → t<h →
      PositiveSemidefinite (dual (inversePencil T t) (B j)) := by
    apply inverse_dual_psd_near_of_segment T (B j) (hfact.2.1 j)
    refine ⟨a,ha,?_⟩
    intro t ht hta
    rw [← hF j]
    exact (hsegment t ht hta).2 j
  obtain ⟨b,hb,hdualAll⟩ := finite_common_psd_interval
    (fun j t => PositiveSemidefinite (dual (inversePencil T t) (B j))) hdual
  obtain ⟨c,hc,hdetAll⟩ := right_segment_of_eventually_nhds _ (pencil_det_eventually_ne_zero T)
  refine ⟨T,min a (min b c),lt_min ha (lt_min hb hc),hE,hF,?_⟩
  intro t ht hth
  have hta : t<a := hth.trans_le (min_le_left a (min b c))
  have htb : t<b := (hth.trans_le (min_le_right a (min b c))).trans_le (min_le_left b c)
  have htc : t<c := (hth.trans_le (min_le_right a (min b c))).trans_le (min_le_right b c)
  have hdet : (1+t • T).det≠0 := hdetAll t ht htc
  refine ⟨hdet,?_⟩
  have hprim : ∀ i, PositiveSemidefinite (primal (1+t • T) (A i)) := by
    intro i
    rw [primal_one_add_smul T t (A i) (hfact.1 i).1,← hE i]
    exact (hsegment t ht hta).1 i
  have hnew := factorization_primal_dual M A B hfact (1+t • T) (inversePencil T t)
    (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)) hprim (hdualAll t ht htb)
  have hprimalEq : (fun i => primal (1+t • T) (A i))=(fun i => A i+t • E i) := by
    funext i
    rw [primal_one_add_smul T t (A i) (hfact.1 i).1,← hE i]
  rw [hprimalEq] at hnew
  exact hnew

#assert_trust kernel integrate_feasible_direction
#print axioms integrate_feasible_direction
end NLA.Proofs.PF05
