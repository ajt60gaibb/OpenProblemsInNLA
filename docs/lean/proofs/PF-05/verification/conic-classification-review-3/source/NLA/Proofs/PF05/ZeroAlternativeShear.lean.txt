import NLA.Proofs.PF05.ZeroAlternativeRaw
import NLA.Proofs.PF05.ZeroCanonical
import NLA.Proofs.PF05.CongruenceTransport

/-! Actual shear and reflection remove the fourth parameter of the actual
finite operator, and the trace pairing determines its exact inverse dual. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05
open NLA.Statements.PF05
noncomputable section

def zeroShear (δ : ℝ) : Sym2 := !![1,0;-δ,1]
def zeroReflection : Sym2 := !![1,0;0,-1]

@[simp] theorem zeroShear_det (δ : ℝ) : (zeroShear δ).det = 1 := by
  simp [zeroShear, Matrix.det_fin_two]
@[simp] theorem zeroReflection_det : zeroReflection.det = -1 := by
  simp [zeroReflection, Matrix.det_fin_two]

theorem zeroShear_primal (α β γ δ : ℝ) (A : Sym2) :
    primalCongruence (zeroShear δ)
      (!![A 0 0 + α * A 0 1 + β * A 1 1, γ * A 0 1 + δ * A 1 1;
        γ * A 0 1 + δ * A 1 1, A 1 1]) =
      zeroCanonicalPrimal (α - 2 * δ * γ) (β - δ ^ 2) γ A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primalCongruence, zeroShear, zeroCanonicalPrimal,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem zeroReflection_primal (α β γ : ℝ) (A : Sym2) :
    primalCongruence zeroReflection (zeroCanonicalPrimal α β γ A) =
      zeroCanonicalPrimal α β (-γ) A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primalCongruence, zeroReflection, zeroCanonicalPrimal,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Every actual alternative with the same normalized distinguished pair
has a canonical primal map after an actual invertible shear/reflection. -/
theorem zeroAlternative_shear {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A At : Fin p → Sym2) (B Bt : Fin q → Sym2)
    (hfact : Factorization M A B) (ht : Factorization M At Bt) (hrank : M.rank = 3)
    (i₀ : Fin p) (j₀ : Fin q)
    (hA : A i₀ = !![1,0;0,0]) (hB : B j₀ = !![0,0;0,1])
    (hAt : At i₀ = !![1,0;0,0]) (hBt : Bt j₀ = !![0,0;0,1]) :
    ∃ (S : Sym2) (α β γ : ℝ), S.det ≠ 0 ∧ 0 < γ ∧
      ∀ i, primalCongruence S (At i) = zeroCanonicalPrimal α β γ (A i) := by
  obtain ⟨α, β, γ, δ, hγ, hraw⟩ :=
    zeroAlternative_raw M A At B Bt hfact ht hrank i₀ j₀ hA hB hAt hBt
  have hshear (i : Fin p) : primalCongruence (zeroShear δ) (At i) =
      zeroCanonicalPrimal (α - 2 * δ * γ) (β - δ ^ 2) γ (A i) := by
    rw [hraw i]
    exact zeroShear_primal α β γ δ (A i)
  by_cases hpos : 0 < γ
  · exact ⟨zeroShear δ, α - 2 * δ * γ, β - δ ^ 2, γ,
      by simp, hpos, hshear⟩
  · refine ⟨zeroShear δ * zeroReflection, α - 2 * δ * γ, β - δ ^ 2, -γ,
      by simp [Matrix.det_mul], by rcases lt_or_gt_of_ne hγ with h | h <;> linarith, ?_⟩
    intro i
    rw [← primalCongruence_comp, hshear, zeroReflection_primal]

/-- The actual canonical primal map forces the exact weighted inverse-dual
formula on every dual factor, by actual rank-three trace separation. -/
theorem zeroCanonical_dual_of_primal {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A At : Fin p → Sym2) (B Bt : Fin q → Sym2)
    (hfact : Factorization M A B) (ht : Factorization M At Bt) (hrank : M.rank = 3)
    (α β γ : ℝ) (hγ : γ ≠ 0)
    (hAt : ∀ i, At i = zeroCanonicalPrimal α β γ (A i)) :
    ∀ j, Bt j = zeroCanonicalDual α β γ (B j) := by
  intro j
  let C := Bt j - zeroCanonicalDual α β γ (B j)
  have hDs : Symmetric (zeroCanonicalDual α β γ (B j)) := by
    intro a b
    fin_cases a <;> fin_cases b <;> rfl
  have hCs : Symmetric C := by
    intro a b
    exact congrArg₂ (fun x y : ℝ => x - y) ((ht.2.1 j).1 a b) (hDs a b)
  have hC : C = 0 := trace_pairing_left_nondegenerate_of_rank_three M At Bt ht hrank C hCs (by
    intro i
    change Matrix.trace (At i * (Bt j - zeroCanonicalDual α β γ (B j))) = 0
    rw [Matrix.mul_sub, Matrix.trace_sub, ← ht.2.2 i j, hAt,
      zeroCanonical_trace α β γ hγ (A i) (B j) (hfact.1 i).1 (hfact.2.1 j).1,
      ← hfact.2.2 i j, sub_self])
  exact sub_eq_zero.mp hC

#assert_trust kernel zeroAlternative_shear
#assert_trust kernel zeroCanonical_dual_of_primal
#print axioms zeroAlternative_shear
#print axioms zeroCanonical_dual_of_primal
end
end NLA.Proofs.PF05
