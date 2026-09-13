/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Mathematical theorem: Matthew J. Colbrook, Sharp Frobenius error transfer for
monotone subhomogeneous matrix functions. This concludes the original universal
claim from its actual difference-of-squared-norms premise, for every allowed basis.
-/
import NLA.RA09.Transfer
import NLA.RA09.ZeroTail

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
noncomputable section
namespace NLA.RA09

theorem concaveFrobeniusTransferConjecture_proved : ConcaveFrobeniusTransferConjecture := by
  intro n _hn k _hkone hk A Ahat hA _hAhat horder f hf dA dHat ε hε hpremise
  by_cases hτ : dA.eigenvalues ⟨k,hk⟩ = 0
  · obtain ⟨_,_,hHat,hOptimal⟩ :=
      zero_tail_closure_proved dA dHat horder f hf k hk hτ ε hε hpremise
    have hnonneg := frobeniusSquared_nonneg
      (functionalCalculus f A-functionTruncation dA f k)
    rw [hOptimal] at hnonneg
    rw [hHat,hOptimal]
    nlinarith [mul_nonneg hε hnonneg]
  · have hτpos : 0 < dA.eigenvalues ⟨k,hk⟩ :=
      lt_of_le_of_ne (dA.nonnegative _) (Ne.symm hτ)
    have htrunc := truncation_semantics_proved dHat k hk.le f
    have hresidual := (trace_deficit_reduction_proved A (truncation dHat k)
      hA htrunc.1 (htrunc.2.1.trans horder)).2.2
    have hown := truncation_semantics_proved dA k hk.le f
    rw [hown.2.2.1] at hpremise
    have hEA : frobeniusSquared (A-truncation dHat k) ≤
        (1+ε)*spectralTail dA k := hresidual.trans hpremise
    obtain ⟨hexcess,htail⟩ := positive_tail_transfer_proved dA dHat horder f hf k hk hτpos
    have hscaled := mul_le_mul_of_nonneg_left
      (show frobeniusSquared (A-truncation dHat k)-spectralTail dA k ≤
        ε*spectralTail dA k by nlinarith [hEA])
      (sq_nonneg (transferScale f (dA.eigenvalues ⟨k,hk⟩)))
    have htailε := mul_le_mul_of_nonneg_left htail hε
    rw [hown.2.2.2.1]
    nlinarith

#assert_trust kernel concaveFrobeniusTransferConjecture_proved
#print axioms concaveFrobeniusTransferConjecture_proved

end NLA.RA09
