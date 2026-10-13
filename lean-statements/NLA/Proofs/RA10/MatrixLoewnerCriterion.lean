import NLA.Proofs.RA10.MatrixDividedDifference
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.Polynomial.Roots

/-! A finite-dimensional divided-difference criterion for matrix monotonicity.
Continuity permits finitely many exceptional scalar arguments. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Matrix Filter Topology Set
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace NLA.Proofs.RA10

theorem finite_exception_deriv_nonneg_le (S : Finset ℝ) {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, x ∉ S → ∃ r, 0 ≤ r ∧ HasDerivAt f r x) : f a ≤ f b := by
  induction S using Finset.induction_on generalizing a b with
  | empty =>
    have hm : MonotoneOn f (Icc a b) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hc
      · intro x hx
        rw [interior_Icc] at hx
        obtain ⟨r, _, hr⟩ := hd x hx (by simp)
        exact hr.differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        obtain ⟨r, hpos, hr⟩ := hd x hx (by simp)
        simpa only [hr.deriv] using hpos
    exact hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  | @insert c S hcS ih =>
    by_cases hc' : c ∈ Ioo a b
    · have hleft : f a ≤ f c := by
        apply ih hc'.1.le (hc.mono (Icc_subset_Icc le_rfl hc'.2.le))
        intro x hx hxS
        exact hd x ⟨hx.1, hx.2.trans hc'.2⟩ (by
          simp only [Finset.mem_insert, not_or]
          exact ⟨ne_of_lt hx.2, hxS⟩)
      have hright : f c ≤ f b := by
        apply ih hc'.2.le (hc.mono (Icc_subset_Icc hc'.1.le le_rfl))
        intro x hx hxS
        exact hd x ⟨hc'.1.trans hx.1, hx.2⟩ (by
          simp only [Finset.mem_insert, not_or]
          exact ⟨ne_of_gt hx.1, hxS⟩)
      exact hleft.trans hright
    · apply ih hab hc
      intro x hx hxS
      apply hd x hx
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun h => hc' (h ▸ hx), hxS⟩

theorem matrix_cfc_diagonal_quadratic_hasDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0))
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) (hd : ∀ i, DifferentiableAt ℝ f (a i))
    {H : Matrix ι ι ℝ} (hH : H.IsHermitian) (v : ι → ℝ) :
    HasDerivAt (fun t : ℝ => star v ⬝ᵥ (cfc f (diagonal a + t • H) *ᵥ v))
      (star v ⬝ᵥ (((fun i j => dslope f (a j) (a i)) ⊙ H) *ᵥ v)) 0 := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  exact ((matrix_cfc_diagonal_hasDerivAt hf ha hd hH i j).mul_const (v j)).const_mul (star (v i))

theorem matrix_cfc_quadratic_hasDerivAt_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0))
    {A H : Matrix ι ι ℝ} (hA : A.PosDef) (hH : H.PosSemidef)
    (hd : ∀ i, DifferentiableAt ℝ f (hA.1.eigenvalues i))
    (hL : Matrix.PosSemidef (fun i j => dslope f (hA.1.eigenvalues j) (hA.1.eigenvalues i)))
    (v : ι → ℝ) :
    ∃ r, 0 ≤ r ∧ HasDerivAt (fun t : ℝ => star v ⬝ᵥ (cfc f (A + t • H) *ᵥ v)) r 0 := by
  let U : Matrix ι ι ℝ := hA.1.eigenvectorUnitary
  let K : Matrix ι ι ℝ := U.transpose * H * U
  let w := U.transpose *ᵥ v
  have hU : U.transpose * U = 1 := by
    simpa only [U, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self hA.1.eigenvectorUnitary
  have hUU := mul_eq_one_comm.mp hU
  have hK : K.PosSemidef := by
    simpa only [K, conjTranspose_eq_transpose_of_trivial] using hH.conjTranspose_mul_mul_same U
  have heq (t : ℝ) : A + t • H =
      U * (diagonal hA.1.eigenvalues + t • K) * U.transpose := by
    have hspec : A = U * diagonal hA.1.eigenvalues * U.transpose := by
      simpa [U, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] using hA.1.spectral_theorem
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, ← hspec]
    congr 1
    simp only [K, Matrix.mul_assoc, ← Matrix.mul_assoc U U.transpose,
      hUU, Matrix.one_mul, Matrix.mul_one]
  have hder := matrix_cfc_diagonal_quadratic_hasDerivAt hf hA.eigenvalues_pos hd hK.1 w
  refine ⟨_, (hL.hadamard hK).dotProduct_mulVec_nonneg w, ?_⟩
  convert hder using 1
  funext t
  rw [heq t, matrix_cfc_orthogonal f
    ((isHermitian_diagonal _).add (hK.1.smul (show IsSelfAdjoint t from rfl))) hU]
  simp only [star_trivial, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, w]

theorem matrix_affine_spectrum_exception_finite {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A H : Matrix ι ι ℝ) (c : ℝ) (hA : IsUnit (A - c • 1)) :
    Set.Finite {t : ℝ | c ∈ spectrum ℝ (A + t • H)} := by
  let M : Matrix ι ι (Polynomial ℝ) := fun i j =>
    Polynomial.C ((A - c • 1) i j) + Polynomial.X * Polynomial.C (H i j)
  let p := Matrix.det M
  have heval (t : ℝ) : p.eval t = (A + t • H - c • 1).det := by
    have hh := (Polynomial.evalRingHom t).map_det M
    change p.eval t = _ at hh
    rw [hh]
    congr 1
    ext i j
    change (M i j).eval t = (A + t • H - c • 1) i j
    simp [M, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
    ring
  have hp : p ≠ 0 := by
    intro hz
    have hh := heval 0
    simp only [hz, Polynomial.eval_zero, zero_smul, add_zero] at hh
    exact (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hA)) hh.symm
  apply (Polynomial.finite_setOfPred_isRoot hp).subset
  intro t ht
  change c ∈ spectrum ℝ (A + t • H) at ht
  change p.eval t = 0
  rw [heval, ← not_ne_iff, ← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
  rw [spectrum.mem_iff] at ht
  simpa only [Algebra.algebraMap_eq_smul_one, ← neg_sub (A + t • H), IsUnit.neg_iff] using ht

theorem matrix_loewner_monotone_of_base_regular {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℝ → ℝ} {c : ℝ} (hf : ContinuousOn f (Ioi 0))
    (hd : ∀ x > 0, x ≠ c → DifferentiableAt ℝ f x)
    (hL : ∀ a : ι → ℝ, (∀ i, 0 < a i) → (∀ i, a i ≠ c) →
      Matrix.PosSemidef (fun i j => dslope f (a j) (a i)))
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (_hB : B.PosDef)
    (hAB : (B - A).PosSemidef) (hreg : IsUnit (A - c • 1)) :
    (cfc f B - cfc f A).PosSemidef := by
  classical
  let H := B - A
  let X : ℝ → Matrix ι ι ℝ := fun t => A + t • H
  have hpos (t : ℝ) (ht : 0 ≤ t) : (X t).PosDef := hA.add_posSemidef (hAB.smul ht)
  have hfinite := matrix_affine_spectrum_exception_finite A H c hreg
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (cfc_predicate f B).sub (cfc_predicate f A)
  · intro v
    let F : ℝ → ℝ := fun t => star v ⬝ᵥ (cfc f (X t) *ᵥ v)
    have hfc : ContinuousOn (fun t => cfc f (X t)) (Icc 0 1) :=
      (matrix_cfc_continuousOn_positive hf).comp (by fun_prop)
        (fun t ht => hpos t ht.1)
    have hq : Continuous (fun M : Matrix ι ι ℝ => star v ⬝ᵥ (M *ᵥ v)) := by
      simp only [dotProduct, mulVec]; fun_prop
    have hcont : ContinuousOn F (Icc 0 1) := hq.comp_continuousOn hfc
    have hle : F 0 ≤ F 1 := by
      apply finite_exception_deriv_nonneg_le hfinite.toFinset zero_le_one hcont
      intro t ht htS
      have hn : c ∉ spectrum ℝ (X t) := by
        simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, X] using htS
      have hXt := hpos t ht.1.le
      have hne (i : ι) : hXt.1.eigenvalues i ≠ c := by
        intro hi
        apply hn
        rw [← hi]
        exact hXt.1.eigenvalues_mem_spectrum_real i
      obtain ⟨r, hr, hdr⟩ := matrix_cfc_quadratic_hasDerivAt_nonneg hf hXt hAB
        (fun i => hd _ (hXt.eigenvalues_pos i) (hne i))
        (hL _ hXt.eigenvalues_pos hne) v
      refine ⟨r, hr, ?_⟩
      have hh : HasDerivAt (fun s : ℝ =>
          star v ⬝ᵥ (cfc f (X t + (s - t) • H) *ᵥ v)) r t := by
        have hdr0 : HasDerivAt (fun s : ℝ => star v ⬝ᵥ (cfc f (X t + s • H) *ᵥ v)) r (t - t) := by
          simpa only [sub_self] using hdr
        simpa only [Function.comp_def, mul_one] using
          hdr0.comp (h := fun s : ℝ => s - t) t ((hasDerivAt_id t).sub_const t)
      have heq : (fun s : ℝ => star v ⬝ᵥ (cfc f (X t + (s - t) • H) *ᵥ v)) = F := by
        funext s
        have hm : X t + (s - t) • H = X s := by dsimp [X]; module
        rw [hm]
      exact heq ▸ hh
    simpa only [F, X, H, zero_smul, add_zero, one_smul, add_sub_cancel,
      Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] using hle

theorem matrix_loewner_monotone {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℝ → ℝ} {c : ℝ} (hf : ContinuousOn f (Ioi 0))
    (hd : ∀ x > 0, x ≠ c → DifferentiableAt ℝ f x)
    (hL : ∀ a : ι → ℝ, (∀ i, 0 < a i) → (∀ i, a i ≠ c) →
      Matrix.PosSemidef (fun i j => dslope f (a j) (a i)))
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : (B - A).PosSemidef) : (cfc f B - cfc f A).PosSemidef := by
  let s : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hspos (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  have hs : Tendsto s atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  have hinj : Function.Injective (fun n : ℕ => c - s n) := by
    intro n m hnm
    have hinv : ((n : ℝ) + 1)⁻¹ = ((m : ℝ) + 1)⁻¹ := sub_right_injective hnm
    have hcast : (n : ℝ) = (m : ℝ) := add_right_cancel (inv_injective hinv)
    exact_mod_cast hcast
  have hfinite := A.finite_real_spectrum.preimage hinj.injOn
  have hregular : ∀ᶠ n : ℕ in atTop, IsUnit (A + s n • 1 - c • 1) := by
    filter_upwards [hfinite.eventually_cofinite_notMem.filter_mono atTop_le_cofinite] with n hn
    by_contra hnu
    apply hn
    change c - s n ∈ spectrum ℝ A
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
    have heq : (c - s n) • (1 : Matrix ι ι ℝ) - A = -(A + s n • 1 - c • 1) := by module
    rw [heq, IsUnit.neg_iff]
    exact hnu
  apply matrix_posSemidef_tendsto
    ((matrix_cfc_shift_tendsto hf hB hs).sub (matrix_cfc_shift_tendsto hf hA hs))
  filter_upwards [hregular] with n hn
  apply matrix_loewner_monotone_of_base_regular hf hd hL
    (hA.add (PosDef.one.smul (hspos n))) (hB.add (PosDef.one.smul (hspos n))) _ hn
  simpa only [add_sub_add_right_eq_sub] using hAB

#assert_trust kernel finite_exception_deriv_nonneg_le
#assert_trust kernel matrix_cfc_diagonal_quadratic_hasDerivAt
#assert_trust kernel matrix_cfc_quadratic_hasDerivAt_nonneg
#assert_trust kernel matrix_affine_spectrum_exception_finite
#assert_trust kernel matrix_loewner_monotone_of_base_regular
#assert_trust kernel matrix_loewner_monotone
#print axioms matrix_loewner_monotone

end NLA.Proofs.RA10
