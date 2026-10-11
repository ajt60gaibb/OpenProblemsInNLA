import OAI.Analysis.DirectCrouzeix.CircleFourier

namespace OAI

universe u_73 u_74 u_75 u_76 u_77 u_78 u_79 u_80 u_81 u_82 u_83 u_84 u_85 u_86

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

theorem matrix_energy_split {ι : Type u_73} {κ : Type u_74} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (f : BoundaryCircle → Matrix ι κ ℂ) (hf : Continuous f) :
    (∫ t, hsSq (f t) ∂circleMeasure) =
      (∑' n : ℕ, hsSq (fourierCoeff f (n+1))) + hsSq (fourierCoeff f 0) +
      ∑' n : ℕ, hsSq (fourierCoeff f (-(n+1))) := by
  have hp := matrix_circle_parseval f hf
  rw [← hp.tsum_eq]
  apply tsum_of_add_one_of_neg_add_one
  · exact hp.summable.comp_injective (by intro i j he; exact_mod_cast (add_right_cancel he : (i : ℤ) = j))
  · exact hp.summable.comp_injective (by intro i j he; exact_mod_cast (add_right_cancel (neg_injective he) : (i : ℤ) = j))

@[simp] theorem hsSq_zero {ι : Type u_75} {κ : Type u_76} [Fintype ι] [Fintype κ] :
    hsSq (0 : Matrix ι κ ℂ) = 0 := by simp [hsSq_eq_sum_norm_sq]

theorem hsSq_add_self {ι : Type u_77} {κ : Type u_78} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) :
    hsSq (A + A) = 4 * hsSq A := by
  rw [← two_smul ℂ A,hsSq_smul]
  norm_num

theorem fourierCoeff_add_star {ι : Type u_79} [Fintype ι] [DecidableEq ι]
    (P Q : BoundaryCircle → Matrix ι ι ℂ) (hP : Continuous P) (hQ : Continuous Q) (k : ℤ) :
    fourierCoeff (fun t => P t + (Q t)ᴴ) k =
      fourierCoeff P k + (fourierCoeff Q (-k))ᴴ := by
  have hQstar := conjugateTransposeCLM.continuous.comp hQ
  have hh := congrFun (fourierCoeff.add (continuous_integrable_compact _ hP)
    (continuous_integrable_compact _ hQstar)) k
  change fourierCoeff (fun t => P t + (Q t)ᴴ) k =
    fourierCoeff P k + fourierCoeff (fun t => (Q t)ᴴ) k at hh
  rwa [fourierCoeff_star_matrix Q hQ k] at hh

theorem anti_matrix_energy {ι : Type u_80} [Fintype ι] [DecidableEq ι]
    (P : BoundaryCircle → Matrix ι ι ℂ) (hP : Continuous P)
    (hpos : ∀ k : ℤ, 0 < k → fourierCoeff P k = 0) :
    (∫ t, hsSq (P t) ∂circleMeasure) = hsSq (fourierCoeff P 0) +
      ∑' n : ℕ, hsSq (fourierCoeff P (-(n+1))) := by
  rw [matrix_energy_split P hP]
  have hp : ∀ n : ℕ, fourierCoeff P (n+1) = 0 := fun n => hpos _ (by omega)
  simp only [hp,hsSq_zero,tsum_zero,zero_add]

theorem anti_diagonal_energy {ι : Type u_81} [Fintype ι] [DecidableEq ι]
    (P : BoundaryCircle → Matrix ι ι ℂ) (hP : Continuous P)
    (hpos : ∀ k : ℤ, 0 < k → fourierCoeff P k = 0)
    (hzero : (fourierCoeff P 0).IsHermitian) :
    (∫ t, hsSq (P t + (P t)ᴴ) ∂circleMeasure) =
      4 * (hsSq (fourierCoeff P 0) +
        (1/2 : ℝ) * ∑' n : ℕ, hsSq (fourierCoeff P (-(n+1)))) := by
  have hcont : Continuous (fun t => P t + (P t)ᴴ) :=
    hP.add (conjugateTransposeCLM.continuous.comp hP)
  rw [matrix_energy_split _ hcont]
  have hp : ∀ n : ℕ, fourierCoeff P (n+1) = 0 := fun n => hpos _ (by omega)
  simp only [fourierCoeff_add_star P P hP hP,neg_zero,hzero.eq,hp,neg_neg,
    Matrix.conjTranspose_zero,zero_add,add_zero,hsSq_conjTranspose,hsSq_add_self]
  ring

theorem anti_cross_energy {ι : Type u_82} [Fintype ι] [DecidableEq ι]
    (M L : BoundaryCircle → Matrix ι ι ℂ) (hM : Continuous M) (hL : Continuous L)
    (hMp : ∀ k : ℤ, 0 < k → fourierCoeff M k = 0)
    (hLp : ∀ k : ℤ, 0 < k → fourierCoeff L k = 0)
    (hzero : (fourierCoeff L 0)ᴴ = fourierCoeff M 0) :
    (∫ t, hsSq (M t) ∂circleMeasure) ≤
      ∫ t, hsSq (M t + (L t)ᴴ) ∂circleMeasure := by
  have hcont : Continuous (fun t => M t + (L t)ᴴ) :=
    hM.add (conjugateTransposeCLM.continuous.comp hL)
  rw [matrix_energy_split _ hcont,anti_matrix_energy M hM hMp]
  have hpM : ∀ n : ℕ, fourierCoeff M (n+1) = 0 := fun n => hMp _ (by omega)
  have hpL : ∀ n : ℕ, fourierCoeff L (n+1) = 0 := fun n => hLp _ (by omega)
  simp_rw [fourierCoeff_add_star M L hM hL,neg_zero,hzero,hpM,neg_neg,hpL,
    Matrix.conjTranspose_zero,zero_add,add_zero,hsSq_conjTranspose,hsSq_add_self]
  have hsum : 0 ≤ ∑' n : ℕ, hsSq (fourierCoeff L (-(n+1))) :=
    tsum_nonneg (fun _ => hsSq_nonneg _)
  nlinarith [hsSq_nonneg (fourierCoeff M 0)]

theorem finite_negative_bessel {ι : Type u_83} {κ : Type u_84} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (P : BoundaryCircle → Matrix ι κ ℂ) (hP : Continuous P) (N : ℕ) :
    (∑ k : Fin N, hsSq (fourierCoeff P (-(k : ℤ)))) ≤
      ∫ t, hsSq (P t) ∂circleMeasure := by
  classical
  let σ : Fin N → ℤ := fun k => -(k : ℤ)
  have hi : Function.Injective σ := by
    intro i j he
    apply Fin.ext
    exact_mod_cast neg_injective he
  have hp := matrix_circle_parseval P hP
  have hh := hp.summable.sum_le_tsum (Finset.univ.image σ) (fun _ _ => hsSq_nonneg _)
  rw [Finset.sum_image (fun i _ j _ he => hi he),hp.tsum_eq] at hh
  exact hh

def faberWeight (k : ℕ) : ℝ := if k = 0 then 1 else 2

theorem faberWeight_pos (k : ℕ) : 0 < faberWeight k := by
  unfold faberWeight
  split <;> norm_num

theorem weighted_sequence_dual {ι : Type u_85} {κ : Type u_86} [Fintype ι] [Fintype κ]
    (P : ℕ → Matrix ι κ ℂ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ N (C : Fin N → Matrix ι κ ℂ),
      ‖∑ k : Fin N, entryPair (P k) (C k)‖ ^ 2 ≤ b * ∑ k : Fin N, faberWeight k * hsSq (C k)) :
    hsSq (P 0) + (1/2 : ℝ) * ∑' n : ℕ, hsSq (P (n+1)) ≤ b := by
  have hsum : ∀ N, ∑ k ∈ Finset.range N, hsSq (P k) / faberWeight k ≤ b := by
    intro N
    have hh := weighted_coefficient_dual (fun k : Fin N => P k)
      (fun k => faberWeight k) (fun k => faberWeight_pos k) b hb (h N)
    rw [← Fin.sum_univ_eq_sum_range (fun k => hsSq (P k) / faberWeight k)]
    exact hh
  have hnon : ∀ k, 0 ≤ hsSq (P k) / faberWeight k :=
    fun k => div_nonneg (hsSq_nonneg _) (faberWeight_pos k).le
  have hsumm : Summable (fun k => hsSq (P k) / faberWeight k) :=
    summable_of_sum_range_le hnon hsum
  have hh := Real.tsum_le_of_sum_range_le hnon hsum
  rw [hsumm.tsum_eq_zero_add] at hh
  have hw0 : faberWeight 0 = 1 := by simp [faberWeight]
  have hw (n : ℕ) : faberWeight (n+1) = 2 := by simp [faberWeight]
  simp only [hw0,hw,div_one] at hh
  rw [tsum_div_const] at hh
  convert hh using 1 ; ring

end DirectCrouzeix

end

end OAI
