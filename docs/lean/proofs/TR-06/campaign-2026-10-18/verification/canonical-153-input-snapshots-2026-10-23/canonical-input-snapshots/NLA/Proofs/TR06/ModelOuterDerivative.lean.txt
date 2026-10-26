import NLA.Proofs.TR06.ModelSemantics
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! The actual derivative of the tensor outer product is the frozen variation. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.Model
open scoped BigOperators
variable {d : ℕ} {n : Fin d → ℕ}
abbrev FactorSpace (d : ℕ) (n : Fin d → ℕ) := (j : Fin d) → Fin (n j) → ℝ

/-- Ordinary factor-entry projection, without changing the tensor norm. -/
def factorEntry (q : NLA.TR06.TensorIndex d n) (j : Fin d) : FactorSpace d n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n j) => ℝ) (q j)).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun k : Fin d => Fin (n k) → ℝ) j)

def outerDerivative (u : FactorSpace d n) :
    FactorSpace d n →L[ℝ] NLA.TR06.Tensor ℝ d n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : NLA.TR06.TensorIndex d n => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun q => ∑ j : Fin d,
      (∏ k ∈ Finset.univ.erase j, u k (q k)) • factorEntry q j))

theorem outerDerivative_apply (u v : FactorSpace d n) :
    outerDerivative u v = NLA.Statements.TR06.OuterVariation u v := by
  ext q
  simp only [outerDerivative,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,PiLp.continuousLinearEquiv_symm_apply,
    ContinuousLinearMap.pi_apply,sum_apply,
    smul_apply,factorEntry,ContinuousLinearMap.proj_apply,
    smul_eq_mul,NLA.Statements.TR06.OuterVariation]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_prod_erase Finset.univ
    (fun k : Fin d => if k=j then v k (q k) else u k (q k)) (Finset.mem_univ j)]
  simp only [ite_true]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
  simp [hkj]

theorem hasFDerivAt_pureTensor (u : FactorSpace d n) :
    HasFDerivAt NLA.TR06.pureTensor (outerDerivative u) u := by
  have hentry (q : NLA.TR06.TensorIndex d n) (j : Fin d) :
      HasFDerivAt (fun x : FactorSpace d n => x j (q j)) (factorEntry q j) u :=
    (factorEntry q j).hasFDerivAt
  have h : HasFDerivAt (fun x : FactorSpace d n =>
      fun q : NLA.TR06.TensorIndex d n => ∏ j : Fin d, x j (q j))
      (ContinuousLinearMap.pi (fun q => ∑ j : Fin d,
        (∏ k ∈ Finset.univ.erase j, u k (q k)) • factorEntry q j)) u := by
    apply hasFDerivAt_pi.mpr
    intro q
    exact HasFDerivAt.finsetProd (fun j _ => hentry q j)
  exact (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp u h

theorem fderiv_pureTensor_apply (u v : FactorSpace d n) :
    fderiv ℝ NLA.TR06.pureTensor u v = NLA.Statements.TR06.OuterVariation u v := by
  rw [(hasFDerivAt_pureTensor u).fderiv,outerDerivative_apply]

#assert_trust kernel outerDerivative_apply
#assert_trust kernel hasFDerivAt_pureTensor
#assert_trust kernel fderiv_pureTensor_apply
#print axioms fderiv_pureTensor_apply
end NLA.Proofs.TR06.Model
