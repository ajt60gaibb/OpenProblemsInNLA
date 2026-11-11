import NLA.Proofs.TR26.SeparablePencilAvoid
import NLA.Proofs.TR26.WronskianPencilDegree
import NLA.Proofs.TR26.FiniteJetFactorLemmas

/-! An actual full-degree Wronskian with exactly one ordinary double root,
on the nonisotropic chart at zero. The remaining roots are simple. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
open Polynomial
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

def monomialWronskianCofactor (D : Polynomial ℂ) (n : ℕ) : Polynomial ℂ :=
  X ^ (n - 3) * (C (n : ℂ) * D - X * D.derivative)

theorem monomialWronskian_eq_X_sq_mul (D : Polynomial ℂ) (n : ℕ) (hn : 3 ≤ n) :
    polynomialWronskian (X ^ n) D = X ^ 2 * monomialWronskianCofactor D n := by
  have h1 : (X : Polynomial ℂ) ^ (n - 1) = X ^ 2 * X ^ (n - 3) := by
    rw [← pow_add]
    congr 1
    omega
  have h2 : (X : Polynomial ℂ) ^ n = X ^ 2 * X ^ (n - 3) * X := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  unfold polynomialWronskian
  rw [Polynomial.derivative_X_pow, h1, h2]
  unfold monomialWronskianCofactor
  ring

theorem monomialWronskianCofactor_natDegree (D : Polynomial ℂ) (hD : D.Monic)
    (n : ℕ) (hn : 3 ≤ n) (hnD : n < D.natDegree) :
    (monomialWronskianCofactor D n).natDegree = n + D.natDegree - 3 := by
  have hW := monicWronskian_natDegree (X ^ n) D (Polynomial.monic_X_pow n) hD
    (by simpa using (by omega : 0 < n)) (by simpa using hnD)
  simp only [Polynomial.natDegree_X_pow] at hW
  have hS : monomialWronskianCofactor D n ≠ 0 := by
    intro hz
    rw [monomialWronskian_eq_X_sq_mul D n hn, hz, mul_zero, Polynomial.natDegree_zero] at hW
    omega
  rw [monomialWronskian_eq_X_sq_mul D n hn,
    Polynomial.natDegree_mul (pow_ne_zero 2 Polynomial.X_ne_zero) hS,
    Polynomial.natDegree_X_pow] at hW
  omega

theorem monomialCofactors_isCoprime (D : Polynomial ℂ) (hsep : D.Separable)
    (hD0 : D.eval 0 ≠ 0) (n : ℕ) (hn : 4 < n) :
    IsCoprime (monomialWronskianCofactor D 3) (monomialWronskianCofactor D n) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ _ _).mpr
  intro r
  change (monomialWronskianCofactor D 3).eval r ≠ 0 ∨
    (monomialWronskianCofactor D n).eval r ≠ 0
  by_cases h0 : (monomialWronskianCofactor D 3).eval r = 0
  · right
    intro h1
    have h0' : 3 * D.eval r - r * D.derivative.eval r = 0 := by
      simpa [monomialWronskianCofactor] using h0
    have hr : r ≠ 0 := by
      intro hz
      rw [hz, zero_mul, sub_zero] at h0'
      exact (mul_ne_zero (by norm_num) hD0) h0'
    have h1' : (n : ℂ) * D.eval r - r * D.derivative.eval r = 0 := by
      have he : r ^ (n - 3) * ((n : ℂ) * D.eval r - r * D.derivative.eval r) = 0 := by
        simpa [monomialWronskianCofactor] using h1
      exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hr)
    have hn3 : (n : ℂ) - 3 ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast (by omega : n ≠ 3))
    have hDz : D.eval r = 0 := by
      apply (mul_eq_zero.mp (show ((n : ℂ) - 3) * D.eval r = 0 by
        linear_combination h1' - h0')).resolve_left hn3
    have hD'z : D.derivative.eval r = 0 := by
      rw [hDz, mul_zero, zero_sub, neg_eq_zero] at h0'
      exact (mul_eq_zero.mp h0').resolve_left hr
    have hne := hsep.aeval_derivative_ne_zero hDz
    exact hne hD'z
  · exact Or.inl h0

theorem cubicCofactor_degree_two_separable :
    (monomialWronskianCofactor (affineDenominator 2) 3).Separable := by
  have hD : affineDenominator 2 = (1 + X ^ 2 + X ^ 4 : Polynomial ℂ) := by
    norm_num [affineDenominatorOver_succ, affineDenominatorOver_zero]
  have hS : monomialWronskianCofactor (affineDenominator 2) 3 =
      (3 + X ^ 2 - X ^ 4 : Polynomial ℂ) := by
    rw [monomialWronskianCofactor, hD]
    simp only [Nat.sub_self, pow_zero, one_mul, Polynomial.derivative_add,
      Polynomial.derivative_one, Polynomial.derivative_X_pow]
    norm_num [Polynomial.C_ofNat]
    ring
  rw [hS, Polynomial.separable_def]
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ _ _).mpr
  intro r
  change (3 + X ^ 2 - X ^ 4 : Polynomial ℂ).eval r ≠ 0 ∨
    (3 + X ^ 2 - X ^ 4 : Polynomial ℂ).derivative.eval r ≠ 0
  by_cases hs : (3 : ℂ) + r ^ 2 - r ^ 4 = 0
  · right
    intro hz
    have hd : 2 * r - 4 * r ^ 3 = 0 := by
      simpa [Polynomial.derivative_pow] using hz
    have hr : r ≠ 0 := by
      intro h
      rw [h] at hs
      norm_num at hs
    have hmul : r * (2 - 4 * r ^ 2) = 0 := by linear_combination hd
    have hquad : r ^ 2 = (1 / 2 : ℂ) := by
      have h := (mul_eq_zero.mp hmul).resolve_left hr
      linear_combination (-1 / 4 : ℂ) * h
    have hfour : r ^ 4 = (1 / 2 : ℂ) ^ 2 := by
      rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hquad]
    rw [hquad, hfour] at hs
    norm_num at hs
  · left
    simpa using hs

theorem exists_nonisotropic_double_Wronskian_numerator {d : ℕ} (hd : 2 ≤ d) :
    ∃ N S : Polynomial ℂ, N.natDegree ≤ 2 * d ∧ S.Separable ∧ S.eval 0 ≠ 0 ∧
      S.natDegree = 4 * d - 4 ∧ polynomialWronskian N (affineDenominator d) = X ^ 2 * S := by
  classical
  let D := affineDenominator d
  have hDdeg : D.natDegree = 2 * d := affineDenominator_natDegree d
  have hDmonic : D.Monic := affineDenominator_monic d
  have hD0 : D.eval 0 ≠ 0 := by rw [affineDenominator_eval_zero]; exact one_ne_zero
  let S0 := monomialWronskianCofactor D 3
  have hS0deg : S0.natDegree = 2 * d := by
    have h := monomialWronskianCofactor_natDegree D hDmonic 3 le_rfl (by omega)
    dsimp [S0]
    omega
  have hS00 : S0.eval 0 ≠ 0 := by
    simp [S0, monomialWronskianCofactor, D, affineDenominator_eval_zero]
  by_cases hd2 : d = 2
  · subst d
    refine ⟨X ^ 3, S0, by simp, ?_, hS00, ?_, ?_⟩
    · exact cubicCofactor_degree_two_separable
    · simpa using hS0deg
    · exact monomialWronskian_eq_X_sq_mul D 3 le_rfl
  · let n := 2 * d - 1
    have hn : 4 < n := by dsimp [n]; omega
    let S1 := monomialWronskianCofactor D n
    have hS1deg : S1.natDegree = 4 * d - 4 := by
      have h := monomialWronskianCofactor_natDegree D hDmonic n (by omega) (by dsimp [n]; omega)
      dsimp [S1, n]
      dsimp [n] at h
      omega
    have hcop : IsCoprime S0 S1 := monomialCofactors_isCoprime D
      (affineDenominator_separable d) hD0 n hn
    obtain ⟨a, _, hsep, hdeg, hzero⟩ := exists_separable_pencil_avoiding_roots S0 S1 hcop
      (by omega) ∅ {0}
    refine ⟨X ^ n + C a * X ^ 3, S1 + C a * S0, ?_, hsep,
      hzero 0 (by simp), by omega, ?_⟩
    · apply Polynomial.natDegree_add_le_of_degree_le
      · simp only [Polynomial.natDegree_X_pow]
        dsimp [n]
        omega
      · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp; omega)
    · have h1 := monomialWronskian_eq_X_sq_mul D n (by omega)
      have h0 := monomialWronskian_eq_X_sq_mul D 3 le_rfl
      change polynomialWronskian (X ^ n + C a * X ^ 3) D = X ^ 2 * (S1 + C a * S0)
      unfold polynomialWronskian at h0 h1 ⊢
      simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
        zero_mul, zero_add]
      dsimp [S0, S1]
      linear_combination h1 + C a * h0

theorem numerator_ne_zero_at_denominator_root_of_separable_cofactor
    (N D S : Polynomial ℂ) (hW : polynomialWronskian N D = X ^ 2 * S)
    (hsep : S.Separable) (r : ℂ) (hr : r ≠ 0) (hDr : D.eval r = 0) :
    N.eval r ≠ 0 := by
  intro hNr
  have hWr : (X ^ 2 * S).eval r = 0 := by
    rw [← hW]
    simp [polynomialWronskian, hDr, hNr]
  have hSr : S.eval r = 0 := by
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at hWr
    exact (mul_eq_zero.mp hWr).resolve_left (pow_ne_zero 2 hr)
  have hW'r : (X ^ 2 * S).derivative.eval r = 0 := by
    rw [← hW, polynomialWronskian_derivative]
    simp [hDr, hNr]
  have hS'r : S.derivative.eval r = 0 := by
    simp only [Polynomial.derivative_mul, Polynomial.derivative_X_pow, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      hSr, mul_zero, zero_add] at hW'r
    exact (mul_eq_zero.mp hW'r).resolve_left (pow_ne_zero 2 hr)
  exact (hsep.aeval_derivative_ne_zero hSr) hS'r

theorem exists_nonisotropic_ordinary_double_Wronskian {d : ℕ} (hd : 2 ≤ d) :
    ∃ H : Parameter d, ∃ S : Polynomial ℂ,
      H ∈ finiteDoubleWronskianImage d ∧
      MvPolynomial.eval H (isotropicEvaluationFactor d) ≠ 0 ∧
      S.Separable ∧ S.eval 0 ≠ 0 ∧ S.natDegree = 4 * d - 4 ∧
      affineWronskian H = X ^ 2 * S := by
  obtain ⟨N, S, hNdeg, hsep, hS0, hSdeg, hW⟩ := exists_nonisotropic_double_Wronskian_numerator hd
  obtain ⟨H, hN⟩ := affineNumerator_surjective_degreeLE d N hNdeg
  have hWH : affineWronskian H = X ^ 2 * S := by
    change polynomialWronskian (affineNumerator H) (affineDenominator d) = _
    rwa [hN]
  have hS : S ≠ 0 := by
    intro hz
    apply hS0
    simp [hz]
  have hH : H ≠ 0 := by
    intro hz
    have hzN : affineNumerator H = 0 := by
      rw [hz]
      exact (affineNumeratorLinear d).map_zero
    have hzero : affineWronskian H = 0 := by
      change (affineNumerator H).derivative * affineDenominator d -
        affineNumerator H * (affineDenominator d).derivative = 0
      rw [hzN]
      simp
    rw [hWH] at hzero
    exact (mul_ne_zero (pow_ne_zero 2 Polynomial.X_ne_zero) hS) hzero
  have hfinite : H ∈ finiteDoubleWronskianImage d := by
    refine ⟨hH, 0, ?_, ?_, ?_⟩
    · rw [affineDenominator_eval_zero]
      exact one_ne_zero
    · simp [hWH]
    · simp [hWH, Polynomial.derivative_pow]
  refine ⟨H, S, hfinite, ?_, hsep, hS0, hSdeg, hWH⟩
  intro hz
  obtain ⟨r, hr, hNr⟩ := (eval_isotropicEvaluationFactor_eq_zero_iff d H).mp hz
  rw [hN] at hNr
  exact numerator_ne_zero_at_denominator_root_of_separable_cofactor N _ S hW hsep r
    (denominator_root_nonzero hr) ((mem_denominatorRoots_iff d r).mp hr) hNr

theorem exists_nonisotropic_transverse_direction {d : ℕ} (hd : 2 ≤ d) :
    ∃ K : Parameter d, (affineWronskian K).eval 0 ≠ 0 ∧
      (affineWronskian K).natDegree ≤ 4 * d - 2 := by
  obtain ⟨K, hK⟩ := affineNumerator_surjective_degreeLE d X (by simp; omega)
  have hW : affineWronskian K = affineDenominator d - X * (affineDenominator d).derivative := by
    change (affineNumerator K).derivative * affineDenominator d -
      affineNumerator K * (affineDenominator d).derivative = _
    rw [hK, Polynomial.derivative_X, one_mul]
  refine ⟨K, ?_, ?_⟩
  · simp [hW, affineDenominator_eval_zero]
  · rw [hW]
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · rw [affineDenominator_natDegree]
      omega
    · apply Polynomial.natDegree_mul_le.trans
      simp only [Polynomial.natDegree_X, Polynomial.natDegree_derivative,
        affineDenominator_natDegree]
      omega

#assert_trust kernel monomialWronskian_eq_X_sq_mul
#assert_trust kernel monomialWronskianCofactor_natDegree
#assert_trust kernel monomialCofactors_isCoprime
#assert_trust kernel cubicCofactor_degree_two_separable
#assert_trust kernel exists_nonisotropic_double_Wronskian_numerator
#assert_trust kernel numerator_ne_zero_at_denominator_root_of_separable_cofactor
#assert_trust kernel exists_nonisotropic_ordinary_double_Wronskian
#assert_trust kernel exists_nonisotropic_transverse_direction
#print axioms exists_nonisotropic_double_Wronskian_numerator
#print axioms exists_nonisotropic_ordinary_double_Wronskian
end NLA.Proofs.TR26
