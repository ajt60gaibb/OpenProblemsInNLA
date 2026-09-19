import NLA.PF03.ConeCoordinates
import NLA.PF03.TriangleCertificate

/-! C14: the entire cone is salient and contains every irrational seed column.
Strict positive barycentric coefficients are the actual checked C09 data.
Sidney Holden: original mathematics. George Stepaniants, Department of Computing
and Mathematical Sciences, California Institute of Technology: formalization;
Codex assistance. Author: /root. -/
set_option autoImplicit false
open scoped BigOperators Classical Matrix
noncomputable section
namespace NLA.PF03

lemma seedColumn_mem_K (i : Fin 7) : seedColumn i ∈ K := by
  apply (K_mem_coordinates (seedColumn i)).2
  refine ⟨fun j a => if j = i then barycentric a else 0, ?_, ?_⟩
  · intro j a
    change 0 ≤ if j = i then barycentric a else 0
    exact ite_nonneg (triangle_certificate.2.2.1 a).le le_rfl
  · have hsum : (∑ j : Fin 7, ∑ a : Fin 3,
        (if j = i then barycentric a else 0) • castVector (generator j a)) =
        ∑ a : Fin 3, barycentric a • castVector (generator i a) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _hb hbi
        simp [hbi]
      · simp
    rw [hsum, local_generator_sum, triangle_barycentric]
    rfl

theorem cone_pointed :
    K ∩ {x : Fin 7 → ℝ | -x ∈ K} = {0} ∧
      ∀ i : Fin 7, seedColumn i ∈ K :=
  ⟨K_inter_neg_eq_zero, seedColumn_mem_K⟩

#print axioms cone_pointed
#assert_trust kernel cone_pointed
end NLA.PF03
