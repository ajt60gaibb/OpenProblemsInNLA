import OAI.Analysis.DirectCrouzeix.ExponentialSupport

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set

open scoped ComplexConjugate Matrix

namespace DirectCrouzeix.Geometry

theorem exists_exponential_outer {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (hv : Convex ℝ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (D : Finset ℂ) (v : D → ℂ) (b : D → ℝ),
      (∀ z ∈ K, expLevel v b z < 1) ∧
      IsCompact {z | expLevel v b z ≤ 1} ∧
      (∀ z, expLevel v b z ≤ 1 → ∃ w ∈ K, ‖z-w‖ < ε) := by
  classical
  obtain ⟨M,hM0,hM⟩ := hK.isBounded.exists_pos_norm_le
  let L := 2*(M+1)
  let C := 1+L+M
  have hC : 0 < C := by dsimp [C,L]; linarith
  let δ := min (1/2) (ε/(2*C))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hδε : δ*C < ε := by
    have hh : δ ≤ ε/(2*C) := min_le_right _ _
    have hc := (le_div_iff₀ (by positivity : 0 < 2*C)).mp hh
    nlinarith
  obtain ⟨D,hD,h1,hm1,hI,hmI,hnet⟩ := exists_axis_net hδ
  let N : ℝ := Fintype.card D
  have hN : 0 ≤ N := by dsimp [N]; positivity
  let t := (N+1)/δ
  have ht : 0 < t := div_pos (by linarith) hδ
  have htδ : t*δ = N+1 := div_mul_cancel₀ _ (ne_of_gt hδ)
  let v : D → ℂ := fun ν => t • (ν:ℂ)
  let b : D → ℝ := fun ν => -t*(convexSupport K ν+δ)
  have he (z : ℂ) (ν : D) : inner ℝ (v ν) z+b ν = t*(inner ℝ (ν:ℂ) z-convexSupport K ν-δ) := by
    dsimp only [v,b]
    rw [real_inner_smul_left]
    ring
  have hsumlt : N*Real.exp (-t*δ) < 1 := by
    rw [neg_mul,htδ,Real.exp_neg,mul_inv_lt_iff₀ (Real.exp_pos _),one_mul]
    linarith [Real.add_one_le_exp (N+1)]
  have hinside (z : ℂ) (hz : z ∈ K) : expLevel v b z < 1 := by
    calc
      expLevel v b z ≤ ∑ _ν : D, Real.exp (-t*δ) := by
        apply Finset.sum_le_sum
        intro ν hν
        rw [he]
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left (le_convexSupport hK hz (ν:ℂ)) (le_of_lt ht)
        nlinarith
      _ = N*Real.exp (-t*δ) := by simp [N]
      _ < 1 := hsumlt
  have hsupport (z : ℂ) (hz : expLevel v b z ≤ 1) (ν : ℂ) (hν : ν ∈ D) :
      inner ℝ ν z ≤ convexSupport K ν+δ := by
    have hh : Real.exp (inner ℝ (v ⟨ν,hν⟩) z+b ⟨ν,hν⟩) ≤ expLevel v b z :=
      Finset.single_le_sum (f := fun i : D => Real.exp (inner ℝ (v i) z+b i))
        (fun i _ => Real.exp_nonneg _) (Finset.mem_univ (⟨ν,hν⟩ : D))
    have hex := (Real.exp_le_one_iff).mp (hh.trans hz)
    rw [he] at hex
    nlinarith
  have hbound (z : ℂ) (hz : expLevel v b z ≤ 1) : ‖z‖ ≤ L := by
    have hh := axis_support_bound hne hM h1 hm1 hI hmI (hsupport z hz)
    dsimp [L]
    linarith
  refine ⟨D,v,b,hinside,?_,?_⟩
  · apply (isCompact_closedBall (0:ℂ) L).of_isClosed_subset
    · exact isClosed_le (expLevel_contDiff v b).continuous continuous_const
    · intro z hz
      exact mem_closedBall_zero_iff.mpr (hbound z hz)
  · intro z hz
    obtain ⟨w,hw,hzw⟩ := direction_net_distance hK hne hv hδ hM hnet (hbound z hz) (hsupport z hz)
    exact ⟨w,hw,lt_of_le_of_lt hzw hδε⟩

end DirectCrouzeix.Geometry

namespace DirectCrouzeix

@[simp] theorem matrixPolynomialValue_coefficientPolynomial {m d : ℕ}
    (B : Fin (d+1) → Matrix (Fin m) (Fin m) ℂ) (z : ℂ) :
    matrixPolynomialValue z (coefficientPolynomial B) = polynomialValue B z := by
  simp only [coefficientPolynomial,map_sum,map_mul,map_pow,matrixPolynomialValue_C,
    matrixPolynomialValue_X,smul_pow,one_pow,Matrix.mul_smul,Matrix.mul_one,polynomialValue]

@[simp] theorem matrixPolynomialValue_smul {m : ℕ} (F : MatrixPolynomial m) (s z : ℂ) :
    matrixPolynomialValue z (s • F) = s • matrixPolynomialValue z F := by
  rw [← smul_one_smul (Matrix (Fin m) (Fin m) ℂ) s F,Polynomial.smul_eq_C_mul,
    map_mul,matrixPolynomialValue_C,Matrix.smul_mul,Matrix.one_mul]

@[simp] theorem tensorPolynomial_smul {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (F : MatrixPolynomial m) (s : ℂ) :
    tensorPolynomial A (s • F) = s • tensorPolynomial A F := by
  rw [← smul_one_smul (Matrix (Fin m) (Fin m) ℂ) s F,Polynomial.smul_eq_C_mul,
    map_mul,tensorPolynomial_C,Matrix.kronecker_smul,Matrix.one_kronecker_one,
    Matrix.smul_mul,Matrix.one_mul]

end DirectCrouzeix

namespace DirectCrouzeix

open Set Filter Metric

end DirectCrouzeix

end

end

end

end

end

end

end

end

end

end OAI
