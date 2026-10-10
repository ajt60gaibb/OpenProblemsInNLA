import OAI.Analysis.DirectCrouzeix.AnalyticCharts

namespace OAI

universe u_135 u_136 u_137

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

namespace DirectCrouzeix.Geometry

variable {ι : Type u_135} [Fintype ι]

def expGradient (v : ι → ℂ) (b : ι → ℝ) (z : ℂ) : ℂ :=
  ∑ i, Real.exp (inner ℝ (v i) z+b i) • v i

theorem expLevel_contDiff (v : ι → ℂ) (b : ι → ℝ) : ContDiff ℝ ⊤ (expLevel v b) := by
  apply ContDiff.sum
  intro i hi
  exact ((innerSL ℝ (v i)).contDiff.add contDiff_const).exp

theorem expLevel_hasFDerivAt (v : ι → ℂ) (b : ι → ℝ) (z : ℂ) :
    HasFDerivAt (expLevel v b) (innerSL ℝ (expGradient v b z)) z := by
  have hh := HasFDerivAt.fun_sum (x := z) (u := Finset.univ) (fun i _ =>
    (((innerSL ℝ (v i)).hasFDerivAt).add_const (b i)).exp)
  convert! hh using 1
  ext w
  simp only [expGradient,innerSL_apply_apply,sum_inner,real_inner_smul_left,sum_apply,smul_apply,smul_eq_mul]

theorem expLevel_first_order (v : ι → ℂ) (b : ι → ℝ) (z w : ℂ) :
    expLevel v b z + inner ℝ (expGradient v b z) (w-z) ≤ expLevel v b w := by
  have hh (i : ι) :
      Real.exp (inner ℝ (v i) z+b i) + Real.exp (inner ℝ (v i) z+b i)*inner ℝ (v i) (w-z) ≤
        Real.exp (inner ℝ (v i) w+b i) := by
    have ht := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (inner ℝ (v i) (w-z)))
      (Real.exp_nonneg (inner ℝ (v i) z+b i))
    rw [← Real.exp_add] at ht
    have he : inner ℝ (v i) z+b i+inner ℝ (v i) (w-z) = inner ℝ (v i) w+b i := by
      rw [inner_sub_right]; ring
    rw [he] at ht
    linarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hh i)
  simpa only [expLevel,expGradient,sum_inner,real_inner_smul_left,Finset.sum_add_distrib] using hs

theorem expGradient_ne_zero (v : ι → ℂ) (b : ι → ℝ) {p a : ℂ}
    (hp : expLevel v b p = 1) (ha : expLevel v b a < 1) : expGradient v b p ≠ 0 := by
  intro he
  have hh := expLevel_first_order v b p a
  rw [he,inner_zero_left,hp,add_zero] at hh
  linarith

theorem expLevel_convex (v : ι → ℂ) (b : ι → ℝ) : ConvexOn ℝ univ (expLevel v b) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a c ha hc hac
  have hh (i : ι) := convexOn_exp.2 (show inner ℝ (v i) x+b i ∈ univ from mem_univ _)
    (show inner ℝ (v i) y+b i ∈ univ from mem_univ _) ha hc hac
  have he (i : ι) : inner ℝ (v i) (a • x+c • y)+b i =
      a*(inner ℝ (v i) x+b i)+c*(inner ℝ (v i) y+b i) := by
    simp only [inner_add_right,inner_smul_right]
    have hb := congrArg (fun u : ℝ => u*b i) hac
    nlinarith
  simp only [expLevel,he]
  simpa [smul_eq_mul,Finset.sum_add_distrib,Finset.mul_sum] using
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hh i)

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

variable {ι : Type u_136} [Fintype ι]

def expComplex (α β γ : ι → ℝ) (z : ℂ × ℂ) : ℂ :=
  ∑ i, Complex.exp ((γ i:ℂ)+(α i:ℂ)*z.1+(β i:ℂ)*z.2)

theorem expComplex_analytic (α β γ : ι → ℝ) (z : ℂ × ℂ) : AnalyticAt ℂ (expComplex α β γ) z := by
  apply Finset.analyticAt_fun_sum
  intro i hi
  exact ((analyticAt_const.add (analyticAt_const.mul analyticAt_fst)).add
    (analyticAt_const.mul analyticAt_snd)).cexp

theorem expComplex_zero (α β γ : ι → ℝ) : expComplex α β γ 0 = (∑ i, Real.exp (γ i):ℝ) := by
  simp [expComplex,Complex.ofReal_exp]

theorem expComplex_conj (α β γ : ι → ℝ) (z : ℂ × ℂ) :
    expComplex α β γ (conj z.1,conj z.2) = conj (expComplex α β γ z) := by
  simp only [expComplex,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem expComplex_real (α β γ : ι → ℝ) (x y : ℝ) :
    expComplex α β γ (x,y) = (∑ i, Real.exp (γ i+α i*x+β i*y):ℝ) := by
  simp [expComplex,Complex.ofReal_exp]

theorem expComplex_hasFDerivAt_zero (α β γ : ι → ℝ) :
    HasFDerivAt (expComplex α β γ)
      (((∑ i, Real.exp (γ i)*α i : ℝ):ℂ) • ContinuousLinearMap.fst ℂ ℂ ℂ +
       ((∑ i, Real.exp (γ i)*β i : ℝ):ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) 0 := by
  have hh := HasFDerivAt.fun_sum (x := (0:ℂ × ℂ)) (u := Finset.univ) (fun i _ =>
    (((hasFDerivAt_const (γ i:ℂ) (0:ℂ × ℂ)).add
      ((hasFDerivAt_fst (𝕜 := ℂ) (p := (0:ℂ × ℂ))).const_mul (α i:ℂ))).add
      ((hasFDerivAt_snd (𝕜 := ℂ) (p := (0:ℂ × ℂ))).const_mul (β i:ℂ))).cexp)
  convert! hh using 1
  apply ContinuousLinearMap.ext
  intro z
  simp [Complex.ofReal_exp,Finset.sum_mul,Finset.sum_add_distrib,mul_assoc]

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

theorem closure_strict_level {f : ℂ → ℝ} (hc : Continuous f)
    (hv : ConvexOn ℝ univ f) {a : ℂ} (ha : f a < 1) :
    closure {z | f z < 1} = {z | f z ≤ 1} := by
  apply Subset.antisymm
  · apply closure_minimal
    · intro z hz
      exact (show f z < 1 from hz).le
    · exact isClosed_le hc continuous_const
  · intro z hz
    let y := fun t : ℝ => (1-t) • z+t • a
    have hy : Continuous y := by fun_prop
    apply mem_closure_of_tendsto (b := 𝓝[>] (0:ℝ)) ((hy.tendsto' 0 z (by simp [y])).mono_left nhdsWithin_le_nhds)
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
    have hh := hv.2 (mem_univ z) (mem_univ a) (sub_nonneg.mpr (le_of_lt ht.2)) (le_of_lt ht.1) (sub_add_cancel 1 t)
    change f (y t) ≤ (1-t)*f z+t*f a at hh
    change f (y t) < 1
    have h1 := mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr (le_of_lt ht.2))
    have h2 := mul_lt_mul_of_pos_left ha ht.1
    nlinarith

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

variable {ι : Type u_137} [Fintype ι]

end DirectCrouzeix.Geometry

end

end

end

end

end

end OAI
