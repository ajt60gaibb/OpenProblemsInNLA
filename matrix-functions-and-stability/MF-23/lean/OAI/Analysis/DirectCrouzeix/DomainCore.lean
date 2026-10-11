import OAI.Analysis.DirectCrouzeix.PolynomialEnergy

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

theorem analytic_domain_core {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℂ) (b : ℕ → Polynomial ℂ) (hb0 : b 0 = 1)
    (h : BoundaryCircle → ℂ) (hh : Continuous h)
    (hexpand : ∀ G : MatrixPolynomial m, ∃ (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      G = faberPolynomial b C)
    (hlower : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      ∑ k, hsSq (C k) ≤ polynomialEnergy h (faberPolynomial b C))
    (hupper : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      polynomialEnergy h (faberPolynomial b C) ≤ ∑ k : Fin N, faberWeight k * hsSq (C k))
    (R : BoundaryCircle → Matrix (Fin n) (Fin n) ℂ) (hR : Continuous R)
    (hcoeff : ∀ k : ℕ, fourierCoeff R (-(k : ℤ)) = Polynomial.aeval A (b k))
    (hposfreq : ∀ k : ℤ, 0 < k → fourierCoeff R k = 0)
    (hpositive : ∀ t, (R t + (R t)ᴴ).PosSemidef)
    (F : MatrixPolynomial m) (hF : ∀ t, ‖matrixPolynomialValue (h t) F‖ ≤ 1) :
    ‖tensorPolynomial A F‖ ≤ 2 := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let γ := ‖tensorPolynomial A F‖
  by_cases hγ0 : γ = 0
  · change γ ≤ 2
    rw [hγ0]
    norm_num
  have hγ : 0 < γ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hγ0)
  let T := Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A F)
  have hT : ‖T‖ = γ := Matrix.l2_opNorm_toEuclideanCLM _
  obtain ⟨x,y,hx,hy,hxy,hyx⟩ := exists_singular_pair T (hT ▸ hγ)
  rw [hT] at hxy hyx
  let X := matrixify x
  let Y := matrixify y
  have hFx : T (hsVector X) = (γ : ℂ) • hsVector Y := by simpa only [X,Y,hsVector_matrixify] using hxy
  have hFy : ContinuousLinearMap.adjoint T (hsVector Y) = (γ : ℂ) • hsVector X := by
    simpa only [X,Y,hsVector_matrixify] using hyx
  let P := fun t => Xᴴ * R t * X
  let Q := fun t => Yᴴ * R t * Y
  let M := fun t => Yᴴ * R t * X
  let L := fun t => Xᴴ * R t * Y
  have hC (U V : Matrix (Fin n) (Fin m) ℂ) :
      Continuous (fun t => Vᴴ * R t * U) := (compressionCLM U V).continuous.comp hR
  have hCp (U V : Matrix (Fin n) (Fin m) ℂ) (k : ℤ) (hk : 0 < k) :
      fourierCoeff (fun t => Vᴴ * R t * U) k = 0 := by
    rw [fourierCoeff_compression U V R hR,hposfreq k hk]
    simp
  have hCc (U V : Matrix (Fin n) (Fin m) ℂ) (k : ℕ) :
      fourierCoeff (fun t => Vᴴ * R t * U) (-(k : ℤ)) = Vᴴ * Polynomial.aeval A (b k) * U := by
    rw [fourierCoeff_compression U V R hR,hcoeff]
  have hC0 (U V : Matrix (Fin n) (Fin m) ℂ) :
      fourierCoeff (fun t => Vᴴ * R t * U) 0 = Vᴴ * U := by
    simpa only [Int.natCast_zero,neg_zero,hb0,map_one,Matrix.mul_one] using hCc U V 0
  let a := ∫ t, hsSq (M t) ∂circleMeasure
  have ha : 0 ≤ a := integral_nonneg (fun _ => hsSq_nonneg _)
  have hapos : 0 < a := by
    have hv := cross_boundary_estimate A b h hexpand hlower R hR hcoeff X Y F
    change ‖inner ℂ (hsVector Y) (T (hsVector X))‖^2 ≤ a * polynomialEnergy h F at hv
    have hyHS : ‖hsVector Y‖ = 1 := by simpa only [Y,hsVector_matrixify] using hy
    rw [hFx,inner_smul_right,inner_self_eq_norm_sq_to_K,hyHS] at hv
    by_contra hnot
    have ha0 : a = 0 := le_antisymm (not_lt.mp hnot) ha
    rw [ha0,zero_mul] at hv
    have hv' : γ^2 ≤ 0 := by simpa using hv
    nlinarith [sq_pos_of_pos hγ]
  have hdiag := singular_diagonal_estimates A b h hh hexpand hlower hupper R hR hcoeff F hF X Y γ hγ hFx hFy
  change (_ ≤ a/γ^2) ∧ (_ ≤ a/γ^2) at hdiag
  have hPE : (∫ t, hsSq (P t + (P t)ᴴ) ∂circleMeasure) ≤ 4*a/γ^2 := by
    rw [anti_diagonal_energy P (hC X X) (hCp X X)]
    · have hc0 := hCc X X 0
      have hcs (k : ℕ) := hCc X X (k+1)
      simp only [Int.natCast_zero,neg_zero,Nat.cast_add,Nat.cast_one] at hc0 hcs
      simp_rw [show P = (fun t => Xᴴ * R t * X) from rfl,hc0,hcs]
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hdiag.1 (by norm_num : (0 : ℝ) ≤ 4)
    · rw [hC0 X X]
      exact Matrix.isHermitian_conjTranspose_mul_self X
  have hQE : (∫ t, hsSq (Q t + (Q t)ᴴ) ∂circleMeasure) ≤ 4*a/γ^2 := by
    rw [anti_diagonal_energy Q (hC Y Y) (hCp Y Y)]
    · have hc0 := hCc Y Y 0
      have hcs (k : ℕ) := hCc Y Y (k+1)
      simp only [Int.natCast_zero,neg_zero,Nat.cast_add,Nat.cast_one] at hc0 hcs
      simp_rw [show Q = (fun t => Yᴴ * R t * Y) from rfl,hc0,hcs]
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hdiag.2 (by norm_num : (0 : ℝ) ≤ 4)
    · rw [hC0 Y Y]
      exact Matrix.isHermitian_conjTranspose_mul_self Y
  have hME : a ≤ ∫ t, hsSq (M t + (L t)ᴴ) ∂circleMeasure := by
    apply anti_cross_energy M L (hC X Y) (hC Y X) (hCp X Y) (hCp Y X)
    rw [hC0 Y X,hC0 X Y]
    simp
  have hEcont (U V U' V' : Matrix (Fin n) (Fin m) ℂ) :
      Continuous (fun t => hsSq (Vᴴ * R t * U + (V'ᴴ * R t * U')ᴴ)) :=
    continuous_hsSq.comp ((hC U V).add (conjugateTransposeCLM.continuous.comp (hC U' V')))
  have hpi := continuous_integrable_compact circleMeasure (hEcont X X X X)
  have hqi := continuous_integrable_compact circleMeasure (hEcont Y Y Y Y)
  have hmi := continuous_integrable_compact circleMeasure (hEcont X Y Y X)
  have hblock : 2 * (∫ t, hsSq (M t + (L t)ᴴ) ∂circleMeasure) ≤
      (∫ t, hsSq (P t + (P t)ᴴ) ∂circleMeasure) +
      ∫ t, hsSq (Q t + (Q t)ᴴ) ∂circleMeasure := by
    rw [← integral_const_mul,← integral_add hpi hqi]
    exact integral_mono (hmi.const_mul 2) (hpi.add hqi)
      (fun t => positive_block_hsSq (positive_compression_blocks (R t) X Y (hpositive t)))
  have hb : 2*a ≤ 8*a/γ^2 := by
    simp only [mul_div_assoc] at hPE hQE ⊢
    linarith
  have hmul := (le_div_iff₀ (sq_pos_of_pos hγ)).mp hb
  change γ ≤ 2
  have hg2 : γ^2 ≤ 4 := by nlinarith [hapos]
  nlinarith

theorem faber_expansion_of_degree {m : ℕ} (hm : 0 < m)
    (b : ℕ → Polynomial ℂ) (hb : ∀ k, (b k).degree = k) (G : MatrixPolynomial m) :
    ∃ (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ), G = faberPolynomial b C := by
  classical
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let S : Polynomial.Sequence (Matrix (Fin m) (Fin m) ℂ) :=
    ⟨fun k => scalarMatrixPolynomial (b k),fun k => by
      rw [scalarMatrixPolynomial,Polynomial.degree_map,hb]⟩
  have hunit (k : ℕ) : IsUnit (S k).leadingCoeff := by
    change IsUnit (scalarMatrixPolynomial (b k)).leadingCoeff
    rw [scalarMatrixPolynomial,Polynomial.leadingCoeff_map]
    apply IsUnit.map
    apply isUnit_iff_ne_zero.mpr
    apply Polynomial.leadingCoeff_ne_zero.mpr
    apply Polynomial.degree_ne_bot.mp
    rw [hb]
    exact WithBot.coe_ne_bot
  let N := G.natDegree+1
  have himage : Set.range (fun k : Fin N => S k) = S '' Set.Iio N := by
    ext p
    constructor
    · rintro ⟨k,rfl⟩
      exact ⟨k,k.isLt,rfl⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨⟨k,hk⟩,rfl⟩
  have hG : G ∈ Submodule.span (Matrix (Fin m) (Fin m) ℂ) (Set.range (fun k : Fin N => S k)) := by
    rw [himage,S.span_degreeLT (fun k _ => hunit k),Polynomial.mem_degreeLT]
    exact lt_of_le_of_lt G.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_self G.natDegree)
  obtain ⟨C,hC⟩ := (Submodule.mem_span_range_iff_exists_fun (Matrix (Fin m) (Fin m) ℂ)).mp hG
  refine ⟨N,C,?_⟩
  rw [← hC]
  simp only [faberPolynomial,Polynomial.smul_eq_C_mul]
  rfl

end DirectCrouzeix

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

end DirectCrouzeix.Faber

end

end

end OAI
