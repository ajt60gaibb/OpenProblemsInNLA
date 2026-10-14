import NLA.Proofs.SP14.SobolevOversampling
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
The physical coefficient realization of the source's weighted one-sided Sobolev
sequence space. Its carrier is Mathlib's complete complex ℓ²; the explicit
coefficient map and norm identity identify it isometrically with sequences
whose `(n+1)^(2s)` energy is finite.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- The normed carrier of the one-sided weighted coefficient space. -/
noncomputable abbrev SobolevCoeff (_s : ℝ) := lp (fun _ : ℕ => ℂ) 2

/-- The actual coefficient represented by a weighted ℓ² vector. -/
noncomputable def physicalCoeff (s : ℝ) (y : SobolevCoeff s) (n : ℕ) : ℂ :=
  Complex.ofReal (((n + 1 : ℕ) : ℝ) ^ (-s)) * y n

/-- The weighted coordinate of a physical coefficient sequence. -/
noncomputable def weightedCoord (s : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  Complex.ofReal (((n + 1 : ℕ) : ℝ) ^ s) * a n

theorem weightedCoord_physicalCoeff (s : ℝ) (y : SobolevCoeff s) (n : ℕ) :
    weightedCoord s (physicalCoeff s y) n = y n := by
  have hn : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hp : ((n + 1 : ℕ) : ℝ) ^ s * ((n + 1 : ℕ) : ℝ) ^ (-s) = 1 := by
    rw [← Real.rpow_add hn]
    simp
  simp only [weightedCoord, physicalCoeff, ← mul_assoc, ← Complex.ofReal_mul, hp,
    Complex.ofReal_one, one_mul]

theorem physicalCoeff_weightedCoord (s : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    Complex.ofReal (((n + 1 : ℕ) : ℝ) ^ (-s)) * weightedCoord s a n = a n := by
  have hn : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hp : ((n + 1 : ℕ) : ℝ) ^ (-s) * ((n + 1 : ℕ) : ℝ) ^ s = 1 := by
    rw [← Real.rpow_add hn]
    simp
  simp only [weightedCoord, ← mul_assoc, ← Complex.ofReal_mul, hp,
    Complex.ofReal_one, one_mul]

/-- The physical coefficient weight is exactly the source's `(n+1)^(2s)` weight. -/
theorem weightedCoord_norm_sq (s : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    ‖weightedCoord s a n‖ ^ 2 =
      (((n + 1 : ℕ) : ℝ) ^ (2 * s)) * ‖a n‖ ^ 2 := by
  have hn : 0 ≤ (((n + 1 : ℕ) : ℝ)) := by positivity
  rw [weightedCoord, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hn _), mul_pow]
  rw [← Real.rpow_mul_natCast hn s 2]
  congr 1
  ring_nf

/-- Exact weighted norm-square identity in the physical coordinates. -/
theorem physicalCoeff_norm_sq (s : ℝ) (y : SobolevCoeff s) :
    ‖y‖ ^ 2 = ∑' n : ℕ,
      (((n + 1 : ℕ) : ℝ) ^ (2 * s)) * ‖physicalCoeff s y n‖ ^ 2 := by
  have hnorm := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) y
  have hnorm' : ‖y‖ ^ 2 = ∑' n : ℕ, ‖y n‖ ^ 2 := by
    calc
      ‖y‖ ^ 2 = ‖y‖ ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ = ∑' n : ℕ, ‖y n‖ ^ 2 := by simpa using hnorm
  calc
    ‖y‖ ^ 2 = ∑' n : ℕ, ‖y n‖ ^ 2 := hnorm'
    _ = ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (2 * s)) * ‖physicalCoeff s y n‖ ^ 2 := by
      apply tsum_congr
      intro n
      rw [← weightedCoord_physicalCoeff s y n, weightedCoord_norm_sq]

/-- Literal physical coefficient sequences having finite source Sobolev energy. -/
def HasFiniteSobolevEnergy (s : ℝ) (a : ℕ → ℂ) : Prop :=
  Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (2 * s)) * ‖a n‖ ^ 2)

/-- The set of literal physical coefficient sequences, with its exact energy predicate. -/
def PhysicalSobolev (s : ℝ) := {a : ℕ → ℂ // HasFiniteSobolevEnergy s a}

noncomputable def toPhysical (s : ℝ) (y : SobolevCoeff s) : PhysicalSobolev s := by
  refine ⟨physicalCoeff s y, ?_⟩
  have hs : Summable (fun n : ℕ => ‖y n‖ ^ 2) := by
    simpa using ((lp.memℓp y).summable (by norm_num : 0 < (2 : ENNReal).toReal))
  have heq : (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (2 * s)) * ‖physicalCoeff s y n‖ ^ 2) =
      (fun n : ℕ => ‖y n‖ ^ 2) := by
    funext n
    rw [← weightedCoord_physicalCoeff s y n, weightedCoord_norm_sq]
  change Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (2 * s)) * ‖physicalCoeff s y n‖ ^ 2)
  rw [heq]
  exact hs

noncomputable def fromPhysical (s : ℝ) (a : PhysicalSobolev s) : SobolevCoeff s := by
  refine ⟨(fun n => weightedCoord s a.1 n), ?_⟩
  have hs : Summable (fun n : ℕ => ‖weightedCoord s a.1 n‖ ^ 2) := by
    simpa only [weightedCoord_norm_sq, HasFiniteSobolevEnergy] using a.2
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).2
  change Summable (fun n : ℕ => ‖weightedCoord s a.1 n‖ ^ (2 : ℝ))
  have heq : (fun n : ℕ => ‖weightedCoord s a.1 n‖ ^ (2 : ℝ)) =
      (fun n : ℕ => ‖weightedCoord s a.1 n‖ ^ 2) := by
    funext n
    exact Real.rpow_natCast _ 2
  rw [heq]
  exact hs

/-- The complete ℓ² carrier is bijective with precisely the physical sequences
of finite `(n+1)^(2s)` energy. -/
noncomputable def physicalEquiv (s : ℝ) : SobolevCoeff s ≃ PhysicalSobolev s where
  toFun := toPhysical s
  invFun := fromPhysical s
  left_inv y := by
    apply lp.ext
    funext n
    exact weightedCoord_physicalCoeff s y n
  right_inv a := by
    apply Subtype.ext
    funext n
    exact physicalCoeff_weightedCoord s a.1 n

end NLA.Proofs.SP14
