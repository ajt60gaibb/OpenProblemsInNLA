import NLA.Proofs.TR14.ProductStabilizer
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! Units span any subspace containing one in a finite dimensional algebra
 over an infinite field. The proof uses the finite spectrum of multiplication;
 it does not assume the ambient algebra is reduced or has finitely many
 subalgebras. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

variable {K B : Type*} [Field K] [CommRing B] [Algebra K B]

/-- The algebra spectrum is the spectrum of its faithful multiplication map. -/
theorem spectrum_lmul_eq (x : B) :
    spectrum K (Algebra.lmul K B x) = spectrum K x := by
  ext c
  simp only [spectrum.mem_iff]
  have heq : algebraMap K (Module.End K B) c - Algebra.lmul K B x =
      Algebra.lmul K B (algebraMap K B c - x) := by
    simp only [map_sub, AlgHom.commutes]
  rw [heq, Algebra.lmul_isUnit_iff]

/-- Finite dimensional algebras have only finitely many bad scalar translates. -/
theorem algebra_finite_spectrum [FiniteDimensional K B] (x : B) : (spectrum K x).Finite := by
  rw [← spectrum_lmul_eq x]
  exact Module.End.finite_spectrum _

/-- A scalar translate of any element is an actual unit. -/
theorem exists_unit_scalar_sub [FiniteDimensional K B] [Infinite K] (x : B) :
    ∃ c : K, IsUnit (algebraMap K B c - x) := by
  obtain ⟨c, hc⟩ := (algebra_finite_spectrum (K := K) x).exists_notMem
  exact ⟨c, spectrum.notMem_iff.mp hc⟩

/-- Source transformation lemma's unit-spanning input, proved for the actual
algebra rather than supplied as an oracle. -/
theorem span_units_eq_of_one_mem [FiniteDimensional K B] [Infinite K] (U : Submodule K B) (hU : (1 : B) ∈ U) :
    Submodule.span K {x : B | x ∈ U ∧ IsUnit x} = U := by
  apply le_antisymm
  · exact Submodule.span_le.mpr fun x hx => hx.1
  · intro x hx
    obtain ⟨c, hc⟩ := exists_unit_scalar_sub (K := K) x
    have hone : (1 : B) ∈ Submodule.span K {x : B | x ∈ U ∧ IsUnit x} :=
      Submodule.subset_span ⟨hU, isUnit_one⟩
    have hscalar : algebraMap K B c ∈ Submodule.span K {x : B | x ∈ U ∧ IsUnit x} := by
      simpa only [Algebra.algebraMap_eq_smul_one] using
        (Submodule.span K {x : B | x ∈ U ∧ IsUnit x}).smul_mem c hone
    have hunit : algebraMap K B c - x ∈
        Submodule.span K {x : B | x ∈ U ∧ IsUnit x} := by
      apply Submodule.subset_span
      exact ⟨U.sub_mem (by simpa only [Algebra.algebraMap_eq_smul_one] using U.smul_mem c hU) hx, hc⟩
    simpa only [sub_sub_cancel] using
      (Submodule.span K {x : B | x ∈ U ∧ IsUnit x}).sub_mem hscalar hunit

#assert_trust kernel span_units_eq_of_one_mem
#print axioms span_units_eq_of_one_mem

end NLA.Proofs.TR14
