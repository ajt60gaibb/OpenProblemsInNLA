import NLA.Proofs.PF05.PositiveQuartic
import NLA.Proofs.PF05.HomogeneousQuartic
import NLA.Proofs.PF05.ConicCongruence
import NLA.Proofs.PF05.CommonChart

/-! The complete strictly positive forward implication, using an actual
common chart, retained ray compression, the signed quartic and actual conic
classification. No local-rigidity or connected-quotient oracle is used. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05
open NLA.Statements.PF05 CoordinateActions
noncomputable section

theorem chart_distinct_rigid_implies_unique {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → M2) (B : Fin q → M2)
    (hf : Factorization M A B) (hrank : M.rank=3) (hpos : ∀ i j, 0<M i j)
    (ha : ∀ i, 0<A i 0 0) (hb : ∀ j, 0<B j 1 1)
    (hda : ∀ i k, SamePositiveRay (A i) (A k) → i=k)
    (hdb : ∀ j k, SamePositiveRay (B j) (B k) → j=k)
    (hRigid : InfinitesimallyRigid A B) : UniqueUpToCongruence M A B := by
  intro At Bt hft
  obtain ⟨L,hL,hleft,_⟩ := factorization_change_of_basis M A At B Bt hf hft hrank
  have hmap : ∀ i, At i=primal L (A i) := by
    intro i
    apply leftVector_injective_symmetric _ _ (hft.1 i).1 (primal_symmetric _ _)
    rw [leftVector_primal]
    funext k
    exact congrArg (fun X : Matrix (Fin p) (Fin 3) ℝ => X i k) hleft
  have hz := rigid_chart_alternativePolynomial_zero M A At B Bt hf hft hrank
    hpos ha hb hda hdb hRigid L hmap
  exact ConicCongruence.congruent_of_conic_alternative M A At B Bt hf hft hrank L hL hmap
    (fun v => alternativePolynomial_zero_outer L hz v)

/-- The full positive case, without distinct-ray or favorable-chart hypotheses. -/
theorem positive_rigid_implies_unique {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → M2) (B : Fin q → M2)
    (hf : Factorization M A B) (hrank : M.rank=3) (hpos : ∀ i j, 0<M i j)
    (hRigid : InfinitesimallyRigid A B) : UniqueUpToCongruence M A B := by
  have hp : 0<p := by have hh := Matrix.rank_le_height M; omega
  have hq : 0<q := by have hh := Matrix.rank_le_width M; omega
  obtain ⟨S,hS,hA,hB⟩ := CommonChart.exists_common_chart A B hf.1 hf.2.1
    (fun i => row_factor_ne_zero_of_positive_entry hf (hpos i ⟨0,hq⟩))
    (fun j => column_factor_ne_zero_of_positive_entry hf (hpos ⟨0,hp⟩ j))
  let Ac := fun i => primalCongruence S (A i)
  let Bc := fun j => dualCongruence S (B j)
  have hc : Factorization M Ac Bc := factorization_congruence M A B hf S hS
  have hRc : InfinitesimallyRigid Ac Bc := infinitesimallyRigid_congruence A B S hS hRigid
  obtain ⟨r,s,cA,cB,hposr,hr,hfr,hda,hdb,hRiff,hUiff⟩ :=
    exists_positive_reduction hc hrank hpos
  have hured : UniqueUpToCongruence (reducedMatrix M cA cB) cA.reduced cB.reduced :=
    chart_distinct_rigid_implies_unique _ _ _ hfr hr hposr
      (fun i => hA (cA.pick i)) (fun j => hB (cB.pick j)) hda hdb (hRiff.mp hRc)
  have huc : UniqueUpToCongruence M Ac Bc := hUiff.mpr hured
  intro At Bt hft
  have hbase : Congruent A Ac B Bc := ⟨S,hS,fun _ => rfl,fun _ => rfl⟩
  exact congruent_trans hbase (huc At Bt hft)

#assert_trust kernel chart_distinct_rigid_implies_unique
#assert_trust kernel positive_rigid_implies_unique
#print axioms positive_rigid_implies_unique
end
end NLA.Proofs.PF05
