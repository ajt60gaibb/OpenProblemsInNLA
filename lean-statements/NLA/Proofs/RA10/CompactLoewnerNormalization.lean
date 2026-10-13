import NLA.Proofs.RA10.OperatorMonotoneNormalization
import NLA.Proofs.RA10.CompactLoewnerTransfer

/-! The representation problem reduces to admissible functions normalized at one.
The normalized construction is supplied by `OperatorMonotoneRepresentation`. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory NLA.Statements.RA10

namespace NLA.Proofs.RA10

theorem hasCompactLoewnerRepresentation_atom (t : LoewnerParameter) :
    HasCompactLoewnerRepresentation (loewnerAtom t) := by
  refine ⟨Measure.dirac t, inferInstance, ?_⟩
  intro x _hx
  simp

theorem hasCompactLoewnerRepresentation_smul {f : ℝ → ℝ}
    (hf : HasCompactLoewnerRepresentation f) {c : ℝ} (hc : 0 ≤ c) :
    HasCompactLoewnerRepresentation (fun x => c * f x) := by
  obtain ⟨μ, hμ, hrep⟩ := hf
  let : IsFiniteMeasure μ := hμ
  refine ⟨ENNReal.ofReal c • μ, μ.smul_finite ENNReal.ofReal_ne_top, ?_⟩
  intro x hx
  rw [integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul]
  exact congrArg (fun y => c * y) (hrep x hx)

theorem hasCompactLoewnerRepresentation_add {f g : ℝ → ℝ}
    (hf : HasCompactLoewnerRepresentation f) (hg : HasCompactLoewnerRepresentation g) :
    HasCompactLoewnerRepresentation (fun x => f x + g x) := by
  obtain ⟨μ, hμ, hf⟩ := hf
  obtain ⟨ν, hν, hg⟩ := hg
  let : IsFiniteMeasure μ := hμ
  let : IsFiniteMeasure ν := hν
  refine ⟨μ + ν, inferInstance, ?_⟩
  intro x hx
  rw [integral_add_measure (loewnerAtom_integrable μ hx) (loewnerAtom_integrable ν hx)]
  exact congrArg₂ (fun u v => u + v) (hf x hx) (hg x hx)

/-- The mass of any representing measure is determined by the value at one. -/
theorem compactLoewnerRepresentation_mass {f : ℝ → ℝ} (μ : Measure LoewnerParameter)
    (hrep : ∀ x : ℝ, 0 ≤ x → f x = ∫ t, loewnerAtom t x ∂μ) :
    f 1 = (μ Set.univ).toReal := by
  rw [hrep 1 (by norm_num)]
  simp [loewnerAtom_at_one, measureReal_def]

/-- Proving existence for normalized admissible functions suffices for the
entire frozen class, including functions vanishing identically on [0,∞). -/
theorem hasCompactLoewnerRepresentation_of_normalized
    (hnormalized : ∀ g : ℝ → ℝ, AdmissibleFunction g → g 1 = 1 →
      HasCompactLoewnerRepresentation g)
    {f : ℝ → ℝ} (hf : AdmissibleFunction f) : HasCompactLoewnerRepresentation f := by
  by_cases h1 : f 1 = 0
  · refine ⟨0, inferInstance, ?_⟩
    intro x hx
    simp [admissibleFunction_eq_zero_of_one_eq_zero hf h1 hx]
  have h1pos : 0 < f 1 := lt_of_le_of_ne (hf.2.1 1 (by norm_num)) (Ne.symm h1)
  obtain ⟨hg, hg1⟩ := admissibleFunction_normalize hf h1pos
  have hrep := hasCompactLoewnerRepresentation_smul
    (hnormalized (fun x => (f 1)⁻¹ * f x) hg hg1) h1pos.le
  have heq : (fun x => f 1 * ((f 1)⁻¹ * f x)) = f := by
    funext x
    rw [← mul_assoc, mul_inv_cancel₀ h1, one_mul]
  rwa [heq] at hrep

/-- Assembly from normalized representation existence, proved separately. -/
theorem target_of_normalized_compactLoewnerRepresentation
    (hnormalized : ∀ g : ℝ → ℝ, AdmissibleFunction g → g 1 = 1 →
      HasCompactLoewnerRepresentation g) : Target :=
  target_of_compactLoewnerRepresentation fun _ hf =>
    hasCompactLoewnerRepresentation_of_normalized hnormalized hf

#assert_trust kernel hasCompactLoewnerRepresentation_atom
#assert_trust kernel hasCompactLoewnerRepresentation_smul
#assert_trust kernel hasCompactLoewnerRepresentation_add
#assert_trust kernel compactLoewnerRepresentation_mass
#assert_trust kernel hasCompactLoewnerRepresentation_of_normalized
#assert_trust kernel target_of_normalized_compactLoewnerRepresentation
#print axioms target_of_normalized_compactLoewnerRepresentation

end NLA.Proofs.RA10
