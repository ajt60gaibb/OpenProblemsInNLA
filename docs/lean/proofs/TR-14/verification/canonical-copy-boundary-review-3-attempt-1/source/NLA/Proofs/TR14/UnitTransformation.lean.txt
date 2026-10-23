import NLA.Proofs.TR14.LinearTransformation
import NLA.Proofs.TR14.UnitScaleAction

/-! Undo the chosen-unit normalization in the TR-14 transformation lemma.
This is the exact per-unit auxiliary space required by the contextual proof. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

variable {K B : Type*} [Field K] [Infinite K] [CommRing B] [Algebra K B]
  [FiniteDimensional K B]

/-- The actual transformation conclusion for every chosen unit in `U`, when
`V` contains one (as do all contextual product factors). -/
theorem linearTransformation_unit (U V : Submodule K B)
    (hV : (1 : B) ∈ V) (a : Bˣ) (ha : (a : B) ∈ U) :
    ∃ S : Subalgebra K B, ∃ T : Submodule K B,
      unitScale a V ≤ T ∧ T ≤ U * V ∧ S.toSubmodule * T ≤ T ∧
        Module.finrank K U + Module.finrank K V ≤
          Module.finrank K T + Module.finrank K S := by
  obtain ⟨S, T, hVT, hTUV, hST, hdim⟩ :=
    linearTransformation_normalized (unitScale a⁻¹ U) V
      (one_mem_unitScale_inv a U ha) hV
  refine ⟨S, unitScale a T, unitScale_mono a hVT, ?_,
    unitScale_stable a S T hST, ?_⟩
  · have h := unitScale_mono a hTUV
    simpa only [unitScale_mul_right, unitScale_scale_inv] using h
  · simpa only [finrank_unitScale] using hdim

#assert_trust kernel linearTransformation_unit
#print axioms linearTransformation_unit

end NLA.Proofs.TR14
