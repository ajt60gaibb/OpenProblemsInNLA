import OAI.Analysis.DirectCrouzeix.SupportNets

namespace OAI

universe u_140 u_141 u_142

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

theorem sphere_lift {E : Type u_140} {F : Type u_141} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [AddCommGroup F] [Module ℝ F] (L : E →ₗ[ℝ] F) (hker : L.ker ≠ ⊥)
    {x : E} (hx : ‖x‖ ≤ 1) : ∃ y : E, ‖y‖ = 1 ∧ L y = L x := by
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by simp [w,norm_smul,norm_ne_zero_iff.mpr hv0]
  have hLw : L w = 0 := by simp [w,show L v = 0 from hv]
  let b := inner ℝ x w
  have hn : 0 ≤ b^2+1-‖x‖^2 := by nlinarith [sq_nonneg b,norm_nonneg x]
  let t := -b+Real.sqrt (b^2+1-‖x‖^2)
  have ht : t^2+2*b*t+‖x‖^2 = 1 := by
    have hs := Real.sq_sqrt hn
    dsimp [t]
    nlinarith
  refine ⟨x+t • w,?_,by simp [hLw]⟩
  have hsq : ‖x+t • w‖^2 = 1 := by
    rw [norm_add_sq_real,inner_smul_right,norm_smul,hw,mul_one,Real.norm_eq_abs,sq_abs]
    change ‖x‖^2+2*(t*b)+t^2 = 1
    nlinarith [ht]
  nlinarith [norm_nonneg (x+t • w)]

abbrev Three := EuclideanSpace ℝ (Fin 3)

def bloch (u v : ℂ) : Three :=
  WithLp.toLp 2 ![2*(conj u*v).re,2*(conj u*v).im,Complex.normSq u-Complex.normSq v]

theorem norm_sq_three (p : Three) : ‖p‖^2 = p 0^2+p 1^2+p 2^2 := by
  simp [EuclideanSpace.norm_sq_eq,Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs,add_assoc]

theorem norm_bloch {u v : ℂ} (h : Complex.normSq u+Complex.normSq v = 1) : ‖bloch u v‖ = 1 := by
  have hm : (conj u*v).re^2+(conj u*v).im^2 = Complex.normSq u*Complex.normSq v := by
    calc
      _ = Complex.normSq (conj u*v) := by simp [Complex.normSq_apply,pow_two]
      _ = _ := by rw [Complex.normSq_mul,Complex.normSq_conj]
  have hsq : ‖bloch u v‖^2 = 1 := by
    rw [norm_sq_three]
    change (2*(conj u*v).re)^2+(2*(conj u*v).im)^2+(Complex.normSq u-Complex.normSq v)^2 = 1
    nlinarith [hm]
  nlinarith [norm_nonneg (bloch u v)]

theorem bloch_surjective_sphere {p : Three} (hp : ‖p‖ = 1) :
    ∃ u v : ℂ, Complex.normSq u+Complex.normSq v = 1 ∧ bloch u v = p := by
  have hsq : p 0^2+p 1^2+p 2^2 = 1 := by rw [← norm_sq_three,hp]; norm_num
  have hz : -1 ≤ p 2 ∧ p 2 ≤ 1 := by constructor <;> nlinarith [sq_nonneg (p 0),sq_nonneg (p 1)]
  by_cases hzero : 1+p 2 = 0
  · have h2 : p 2 = -1 := by linarith
    have h0 : p 0 = 0 := by nlinarith [sq_nonneg (p 1)]
    have h1 : p 1 = 0 := by nlinarith [sq_nonneg (p 0)]
    refine ⟨0,1,by norm_num,?_⟩
    ext i
    fin_cases i <;> simp [bloch,h0,h1,h2]
  · let s := (1+p 2)/2
    have hs : 0 < s := by dsimp [s]; exact div_pos (lt_of_le_of_ne (by linarith) (Ne.symm hzero)) (by norm_num)
    let a := Real.sqrt s
    have ha : 0 < a := Real.sqrt_pos.mpr hs
    have ha0 : a ≠ 0 := ne_of_gt ha
    have ha2 : a^2 = s := Real.sq_sqrt hs.le
    let u : ℂ := a
    let v : ℂ := ⟨p 0/(2*a),p 1/(2*a)⟩
    have hu : Complex.normSq u = s := by simp [u,Complex.normSq_apply]; nlinarith [ha2]
    have hv : Complex.normSq v = 1-s := by
      dsimp [v]
      field_simp
      dsimp [s] at *
      nlinarith [hsq,ha2]
    have hw : conj u*v = (⟨p 0/2,p 1/2⟩ : ℂ) := by
      apply Complex.ext <;> simp [u,v,Complex.mul_re,Complex.mul_im] <;> field_simp
    refine ⟨u,v,by rw [hu,hv]; ring,?_⟩
    ext i
    fin_cases i <;> simp [bloch,hw,hu,hv,s] <;> ring

def threeLinear (c : Fin 3 → ℂ) : Three →ₗ[ℝ] ℂ where
  toFun p := ∑ i, (p i : ℂ)*c i
  map_add' p q := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' a p := by simp [Complex.real_smul,Finset.mul_sum,mul_assoc]

theorem threeLinear_ker_ne_bot (c : Fin 3 → ℂ) : (threeLinear c).ker ≠ ⊥ := by
  apply LinearMap.ker_ne_bot_of_finrank_lt
  simp [Complex.finrank_real_complex,finrank_euclideanSpace]

def twoForm (a b c d u v : ℂ) : ℂ :=
  Complex.normSq u * a + Complex.normSq v * d + (conj u*v)*b + (conj v*u)*c

theorem twoForm_bloch (a b c d u v : ℂ) (h : Complex.normSq u+Complex.normSq v = 1) :
    twoForm a b c d u v = (a+d)/2 +
      threeLinear ![(b+c)/2,Complex.I*(b-c)/2,(a-d)/2] (bloch u v) := by
  have hh : (Complex.normSq u : ℂ)+(Complex.normSq v : ℂ) = 1 := by exact_mod_cast h
  have hw : conj v*u = conj (conj u*v) := by simp [mul_comm]
  simp only [twoForm,threeLinear,LinearMap.coe_mk,AddHom.coe_mk]
  change _ = (a+d)/2 + (((2*(conj u*v).re : ℝ):ℂ)*((b+c)/2) +
    (((2*(conj u*v).im : ℝ):ℂ)*(Complex.I*(b-c)/2) +
      (((Complex.normSq u-Complex.normSq v : ℝ):ℂ)*((a-d)/2) + 0)))
  rw [hw]
  apply Complex.ext
  · simp [Complex.mul_re,Complex.mul_im]
    linear_combination ((a.re+d.re)/2)*h
  · simp [Complex.mul_re,Complex.mul_im]
    linear_combination ((a.im+d.im)/2)*h

theorem convex_twoForm (a b c d : ℂ) :
    Convex ℝ {z : ℂ | ∃ u v : ℂ, Complex.normSq u+Complex.normSq v = 1 ∧ twoForm a b c d u v = z} := by
  intro x hx y hy r s hr hs hrs
  obtain ⟨u,v,huv,rfl⟩ := hx
  obtain ⟨w,z,hwz,rfl⟩ := hy
  let L := threeLinear ![(b+c)/2,Complex.I*(b-c)/2,(a-d)/2]
  have hn : ‖r • bloch u v+s • bloch w z‖ ≤ 1 := by
    calc
      _ ≤ ‖r • bloch u v‖+‖s • bloch w z‖ := norm_add_le _ _
      _ = r+s := by rw [norm_smul,norm_smul,norm_bloch huv,norm_bloch hwz,
        Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hr,abs_of_nonneg hs]; ring
      _ = 1 := hrs
  obtain ⟨p,hp,hLp⟩ := sphere_lift L (threeLinear_ker_ne_bot _) hn
  obtain ⟨α,β,hαβ,rfl⟩ := bloch_surjective_sphere hp
  refine ⟨α,β,hαβ,?_⟩
  rw [twoForm_bloch a b c d α β hαβ,twoForm_bloch a b c d u v huv,twoForm_bloch a b c d w z hwz]
  change (a+d)/2+L (bloch α β) = _
  rw [hLp,map_add,map_smul,map_smul]
  simp only [smul_add]
  rw [add_add_add_comm (r • ((a+d)/2)) (r • L (bloch u v)),← add_smul,hrs,one_smul]

section Inner

variable {E : Type u_142} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem orthonormal_pair_norm_sq {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℂ x y = 0) (u v : ℂ) :
    ‖u • x+v • y‖^2 = Complex.normSq u+Complex.normSq v := by
  rw [norm_add_sq (𝕜 := ℂ),inner_smul_left,inner_smul_right,hxy,mul_zero,mul_zero]
  simp only [map_zero,mul_zero,add_zero,norm_smul,hx,hy,mul_one,Complex.normSq_eq_norm_sq]

theorem twoForm_inner {x y : E} (T : E →ₗ[ℂ] E) (u v : ℂ) :
    inner ℂ (u • x+v • y) (T (u • x+v • y)) =
      twoForm (inner ℂ x (T x)) (inner ℂ x (T y)) (inner ℂ y (T x)) (inner ℂ y (T y)) u v := by
  simp only [map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
    twoForm]
  have hu : (Complex.normSq u : ℂ) = conj u*u := by rw [Complex.conj_mul',Complex.normSq_eq_norm_sq,Complex.ofReal_pow]
  have hv : (Complex.normSq v : ℂ) = conj v*v := by rw [Complex.conj_mul',Complex.normSq_eq_norm_sq,Complex.ofReal_pow]
  rw [hu,hv]
  ring

theorem convex_quadratic_range (T : E →ₗ[ℂ] E) :
    Convex ℝ {z : ℂ | ∃ x : E, ‖x‖ = 1 ∧ inner ℂ x (T x) = z} := by
  intro z hz w hw r s hr hs hrs
  obtain ⟨x,hx,rfl⟩ := hz
  obtain ⟨y,hy,rfl⟩ := hw
  let a := inner ℂ x y
  let v := y-a • x
  have hvorth : inner ℂ x v = 0 := by
    simp [v,a,inner_self_eq_norm_sq_to_K,hx]
  by_cases hv0 : v = 0
  · have hey : y = a • x := sub_eq_zero.mp hv0
    have han : ‖a‖ = 1 := by simpa [hey,norm_smul,hx] using hy
    have heq : inner ℂ y (T y) = inner ℂ x (T x) := by
      rw [hey,map_smul,inner_smul_left,inner_smul_right,← mul_assoc,Complex.conj_mul',han]
      simp
    refine ⟨x,hx,?_⟩
    rw [heq,← add_smul,hrs,one_smul]
  · let b : ℂ := ‖v‖
    let e := b⁻¹ • v
    have hb : b ≠ 0 := by dsimp [b]; exact_mod_cast norm_ne_zero_iff.mpr hv0
    have he : ‖e‖ = 1 := norm_smul_inv_norm hv0
    have hxe : inner ℂ x e = 0 := by simp [e,hvorth]
    have hyeq : y = a • x+b • e := by
      simp only [e,smul_smul,mul_inv_cancel₀ hb,one_smul,v]
      abel
    have hab : Complex.normSq a+Complex.normSq b = 1 := by
      rw [← orthonormal_pair_norm_sq hx he hxe a b,← hyeq,hy]
      norm_num
    let A := inner ℂ x (T x)
    let B := inner ℂ x (T e)
    let C := inner ℂ e (T x)
    let D := inner ℂ e (T e)
    have hxF : ∃ u v : ℂ, Complex.normSq u+Complex.normSq v = 1 ∧ twoForm A B C D u v = inner ℂ x (T x) := by
      exact ⟨1,0,by norm_num,by simp [twoForm,A]⟩
    have hyF : ∃ u v : ℂ, Complex.normSq u+Complex.normSq v = 1 ∧ twoForm A B C D u v = inner ℂ y (T y) := by
      refine ⟨a,b,hab,?_⟩
      rw [hyeq,twoForm_inner]
    obtain ⟨u,v,huv,hform⟩ := convex_twoForm A B C D hxF hyF hr hs hrs
    refine ⟨u • x+v • e,?_,?_⟩
    · have hn := orthonormal_pair_norm_sq hx he hxe u v
      rw [huv] at hn
      nlinarith [norm_nonneg (u • x+v • e)]
    · rw [twoForm_inner]
      exact hform

end Inner

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

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
