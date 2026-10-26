import NLA.Proofs.PF05.Congruence
import NLA.Proofs.PF05.PositiveReduction

/-! Exact canonical zero-pair maps and their actual PSD endpoints. The
endpoint identities cover singular, flat and zero factors uniformly. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.PF05
open NLA.Statements.PF05
noncomputable section

/-- The canonical primal alternative, in actual matrix coordinates. -/
def zeroCanonicalPrimal (α β γ : ℝ) (A : Sym2) : Sym2 :=
  !![A 0 0 + α * A 0 1 + β * A 1 1, γ * A 0 1;
    γ * A 0 1, A 1 1]

/-- The inverse dual of the canonical primal map for the trace pairing. -/
def zeroCanonicalDual (α β γ : ℝ) (B : Sym2) : Sym2 :=
  !![B 0 0, (B 0 1 - α * B 0 0 / 2) / γ;
    (B 0 1 - α * B 0 0 / 2) / γ, B 1 1 - β * B 0 0]

/-- The actual proposed primal straight direction. -/
def zeroPrimalDirection (α β γ : ℝ) (A : Sym2) : Sym2 :=
  !![-(γ ^ 2 - 1) * A 0 0 + α * A 0 1 + β * A 1 1, 0; 0, 0]

/-- The actual proposed dual straight direction. -/
def zeroDualDirection (α β γ : ℝ) (B : Sym2) : Sym2 :=
  !![(γ ^ 2 - 1) * B 0 0, -α * B 0 0 / 2;
    -α * B 0 0 / 2, -β * B 0 0]

theorem zeroPrimalDirection_symmetric (α β γ : ℝ) (A : Sym2) :
    Symmetric (zeroPrimalDirection α β γ A) := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem zeroDualDirection_symmetric (α β γ : ℝ) (B : Sym2) :
    Symmetric (zeroDualDirection α β γ B) := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Actual derivative trace cancellation, including its off-diagonal weight. -/
theorem zeroDirection_trace (α β γ : ℝ) (A B : Sym2)
    (hA : Symmetric A) (_hB : Symmetric B) :
    Matrix.trace (zeroPrimalDirection α β γ A * B) +
      Matrix.trace (A * zeroDualDirection α β γ B) = 0 := by
  simp [zeroPrimalDirection, zeroDualDirection, Matrix.trace_fin_two,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hA 1 0]
  ring

/-- The canonical dual really is the inverse dual for the trace pairing. -/
theorem zeroCanonical_trace (α β γ : ℝ) (hγ : γ ≠ 0) (A B : Sym2)
    (hA : Symmetric A) (hB : Symmetric B) :
    Matrix.trace (zeroCanonicalPrimal α β γ A * zeroCanonicalDual α β γ B) =
      Matrix.trace (A * B) := by
  simp [zeroCanonicalPrimal, zeroCanonicalDual, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, hA 1 0, hB 1 0]
  field_simp
  ring

/-- The primal line has a genuinely PSD endpoint obtained from the
actual canonical alternative by one diagonal congruence. -/
theorem zeroPrimalDirection_endpoint (α β γ : ℝ) (hγ : γ ≠ 0)
    (A : Sym2) (hA : Symmetric A) :
    A + (γ ^ 2)⁻¹ • zeroPrimalDirection α β γ A =
      primalCongruence (!![γ⁻¹, 0; 0, 1]) (zeroCanonicalPrimal α β γ A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zeroPrimalDirection, zeroCanonicalPrimal, primalCongruence,
      Matrix.mul_apply, Fin.sum_univ_two, hA 1 0, smul_eq_mul] <;>
    field_simp [hγ]
  all_goals ring

/-- The dual line's unit-time endpoint is also a genuine congruence of
its actual alternative, so flat rank-one factors cause no exception. -/
theorem zeroDualDirection_endpoint (α β γ : ℝ) (hγ : γ ≠ 0)
    (B : Sym2) (hB : Symmetric B) :
    B + zeroDualDirection α β γ B =
      primalCongruence (!![γ, 0; 0, 1]) (zeroCanonicalDual α β γ B) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zeroDualDirection, zeroCanonicalDual, primalCongruence,
      Matrix.mul_apply, Fin.sum_univ_two, hB 1 0] <;>
    field_simp [hγ]
  all_goals ring

/-- Literal PSD convexity, in the frozen quadratic-form convention. -/
theorem psd_add_two (A B : Sym2) (hA : PositiveSemidefinite A)
    (hB : PositiveSemidefinite B) : PositiveSemidefinite (A + B) := by
  exact (psd_iff_posSemidef _).mpr
    (((psd_iff_posSemidef _).mp hA).add ((psd_iff_posSemidef _).mp hB))

/-- A PSD endpoint supplies the whole actual straight segment. -/
theorem psd_line_of_endpoint (A E : Sym2) (h : ℝ) (hh : 0 < h)
    (hA : PositiveSemidefinite A) (hE : PositiveSemidefinite (A + h • E))
    (t : ℝ) (ht : 0 ≤ t) (hth : t ≤ h) :
    PositiveSemidefinite (A + t • E) := by
  have hu : 0 ≤ t / h := div_nonneg ht hh.le
  have hu1 : t / h ≤ 1 := (div_le_one hh).mpr hth
  have hp := psd_add_two ((1 - t / h) • A) ((t / h) • (A + h • E))
    (psd_smul_of_nonneg A hA _ (sub_nonneg.mpr hu1))
    (psd_smul_of_nonneg _ hE _ hu)
  convert hp using 1
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp [ne_of_gt hh]
  ring

#assert_trust kernel zeroDirection_trace
#assert_trust kernel zeroCanonical_trace
#assert_trust kernel zeroPrimalDirection_endpoint
#assert_trust kernel zeroDualDirection_endpoint
#assert_trust kernel psd_line_of_endpoint
#print axioms zeroPrimalDirection_endpoint
#print axioms psd_line_of_endpoint

end
end NLA.Proofs.PF05
