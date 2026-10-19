import NLA.Proofs.TR14.GraphNormalization

/-! Actual scalar surjectivity and nonzero coefficients exclude a stabilizing
multiplier with zero quotient component. Applied to actual primitive
indicators this proves no primitive block is supported only on scalar
summand coordinates. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- The quotient projection is injective on stabilizing multipliers under
the actual scalar-coordinate hypotheses of the ordinary graph construction. -/
theorem stabilizer_eq_zero_of_fst_eq_zero {r : ℕ}
    (Λ : (A × (Fin r → ℂ)) →ₗ[ℂ] ℂ) (W : Submodule ℂ (A × (Fin r → ℂ)))
    (hann : ∀ w ∈ W, Λ w = 0)
    (hscalar : ∀ j : Fin r, Λ (0, Pi.single j 1) ≠ 0)
    (honto : W.map (AlgHom.snd ℂ A (Fin r → ℂ)).toLinearMap = ⊤)
    (e : A × (Fin r → ℂ)) (he : e ∈ productStabilizer W) (heA : e.1 = 0) : e = 0 := by
  classical
  apply Prod.ext heA
  funext j
  have hsingle : Pi.single j (1 : ℂ) ∈
      W.map (AlgHom.snd ℂ A (Fin r → ℂ)).toLinearMap := by rw [honto]; exact Submodule.mem_top
  obtain ⟨w, hw, hwC⟩ := hsingle
  change w.2 = Pi.single j (1 : ℂ) at hwC
  have hew : e * w = e.2 j • (0, Pi.single j (1 : ℂ)) := by
    apply Prod.ext
    · simp [heA]
    · funext k
      by_cases h : j = k
      · subst k
        simp [hwC]
      · simp [hwC, Pi.single_eq_of_ne' h]
  have hzero := hann _ (he w hw)
  rw [hew, map_smul, smul_eq_mul] at hzero
  exact (mul_eq_zero.mp hzero).resolve_right (hscalar j)

/-- Every nonzero primitive indicator therefore has a nonzero actual
quotient component; no separate block-support premise is assumed. -/
theorem stabilizer_fst_ne_zero {r : ℕ}
    (Λ : (A × (Fin r → ℂ)) →ₗ[ℂ] ℂ) (W : Submodule ℂ (A × (Fin r → ℂ)))
    (hann : ∀ w ∈ W, Λ w = 0)
    (hscalar : ∀ j : Fin r, Λ (0, Pi.single j 1) ≠ 0)
    (honto : W.map (AlgHom.snd ℂ A (Fin r → ℂ)).toLinearMap = ⊤)
    (e : A × (Fin r → ℂ)) (he : e ∈ productStabilizer W) (hne : e ≠ 0) : e.1 ≠ 0 := by
  intro hz
  exact hne (stabilizer_eq_zero_of_fst_eq_zero Λ W hann hscalar honto e he hz)

#assert_trust kernel stabilizer_eq_zero_of_fst_eq_zero
#assert_trust kernel stabilizer_fst_ne_zero
#print axioms stabilizer_fst_ne_zero

end NLA.Proofs.TR14
