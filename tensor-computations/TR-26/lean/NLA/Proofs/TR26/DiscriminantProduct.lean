import NLA.Proofs.TR26.FixedDiscriminantAffine

/-! A discriminant product identity with every resultant sign retained. Both
factors have positive degree, as required by Mathlib's normalization. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
namespace NLA.Proofs.TR26.BinaryDiscriminant
open Polynomial

def discriminantSign (n : ℕ) : ℂ := (-1 : ℂ)^(n*(n-1)/2)

theorem discriminantSign_sq (n : ℕ) : discriminantSign n * discriminantSign n = 1 := by
  simp only [discriminantSign,← pow_add,← two_mul,pow_mul]
  norm_num

theorem resultant_product_derivative (f g : Polynomial ℂ)
    (hf : 0 < f.natDegree) (hg : 0 < g.natDegree) :
    Polynomial.resultant (f*g) (f*g).derivative (f.natDegree+g.natDegree)
      (f.natDegree+g.natDegree-1) =
    Polynomial.resultant f f.derivative f.natDegree (f.natDegree-1) *
      Polynomial.resultant g g.derivative g.natDegree (g.natDegree-1) *
      (-1 : ℂ)^(f.natDegree*g.natDegree) *
      Polynomial.resultant f g f.natDegree g.natDegree ^ 2 := by
  have hf0 : f ≠ 0 := by intro h; simp [h] at hf
  have hg0 : g ≠ 0 := by intro h; simp [h] at hg
  have hfg : (f*g).natDegree=f.natDegree+g.natDegree := natDegree_mul hf0 hg0
  have hder : (f*g).derivative.natDegree ≤ f.natDegree+g.natDegree-1 := by
    rw [natDegree_derivative,hfg]
  rw [Polynomial.resultant_mul_left _ _ _ _ hder]
  have hleft : Polynomial.resultant f (f*g).derivative f.natDegree
      (f.natDegree+g.natDegree-1) =
      Polynomial.resultant f f.derivative f.natDegree (f.natDegree-1) *
        Polynomial.resultant f g f.natDegree g.natDegree := by
    have h := Polynomial.resultant_add_mul_right f (f.derivative*g) g.derivative
      f.natDegree (f.natDegree+g.natDegree-1)
      (by rw [natDegree_derivative]; omega) le_rfl
    rw [← derivative_mul] at h
    rw [h]
    have hd : f.derivative.natDegree+g.natDegree=f.natDegree+g.natDegree-1 := by
      rw [natDegree_derivative]; omega
    rw [← hd,Polynomial.resultant_mul_right _ _ _ _ le_rfl,natDegree_derivative]
  have hright : Polynomial.resultant g (f*g).derivative g.natDegree
      (f.natDegree+g.natDegree-1) =
      Polynomial.resultant g g.derivative g.natDegree (g.natDegree-1) *
        Polynomial.resultant g f g.natDegree f.natDegree := by
    have h := Polynomial.resultant_add_mul_right g (g.derivative*f) f.derivative
      g.natDegree (f.natDegree+g.natDegree-1)
      (by rw [natDegree_derivative]; omega) le_rfl
    have heq : g.derivative*f+g*f.derivative=(f*g).derivative := by rw [derivative_mul]; ring
    rw [heq] at h
    rw [h]
    have hd : g.derivative.natDegree+f.natDegree=f.natDegree+g.natDegree-1 := by
      rw [natDegree_derivative]; omega
    rw [← hd,Polynomial.resultant_mul_right _ _ _ _ le_rfl,natDegree_derivative]
  rw [hleft,hright,Polynomial.resultant_comm g f]
  rw [mul_comm g.natDegree f.natDegree]
  ring

theorem discr_mul_with_sign (f g : Polynomial ℂ)
    (hf : 0 < f.natDegree) (hg : 0 < g.natDegree) :
    (f*g).discr =
      discriminantSign (f.natDegree+g.natDegree) *
      discriminantSign f.natDegree * discriminantSign g.natDegree *
      (-1 : ℂ)^(f.natDegree*g.natDegree) *
      f.discr*g.discr*Polynomial.resultant f g f.natDegree g.natDegree ^ 2 := by
  have hf0 : f ≠ 0 := by intro h; simp [h] at hf
  have hg0 : g ≠ 0 := by intro h; simp [h] at hg
  have hfg : (f*g).natDegree=f.natDegree+g.natDegree := natDegree_mul hf0 hg0
  have hld : f.leadingCoeff*g.leadingCoeff ≠ 0 :=
    mul_ne_zero (leadingCoeff_ne_zero.mpr hf0) (leadingCoeff_ne_zero.mpr hg0)
  have hprod := resultant_product_derivative f g hf hg
  have hresfg := Polynomial.resultant_deriv (f := f*g)
    (by rw [← natDegree_pos_iff_degree_pos,hfg]; omega)
  have hresf := Polynomial.resultant_deriv (f := f) (by rwa [← natDegree_pos_iff_degree_pos])
  have hresg := Polynomial.resultant_deriv (f := g) (by rwa [← natDegree_pos_iff_degree_pos])
  rw [hfg] at hresfg
  rw [hresfg,hresf,hresg,Polynomial.leadingCoeff_mul] at hprod
  change discriminantSign (f.natDegree+g.natDegree) *
      (f.leadingCoeff*g.leadingCoeff) * (f*g).discr =
      (discriminantSign f.natDegree*f.leadingCoeff*f.discr) *
      (discriminantSign g.natDegree*g.leadingCoeff*g.discr) *
      (-1:ℂ)^(f.natDegree*g.natDegree) *
      Polynomial.resultant f g f.natDegree g.natDegree ^ 2 at hprod
  have hh := congrArg (discriminantSign (f.natDegree+g.natDegree) * ·) hprod
  have hs := discriminantSign_sq (f.natDegree+g.natDegree)
  apply mul_left_cancel₀ hld
  calc
    _ = (discriminantSign (f.natDegree+g.natDegree) *
        discriminantSign (f.natDegree+g.natDegree)) *
        (f.leadingCoeff*g.leadingCoeff) * (f*g).discr := by rw [hs,one_mul]
    _ = discriminantSign (f.natDegree+g.natDegree) *
        ((discriminantSign f.natDegree*f.leadingCoeff*f.discr) *
        (discriminantSign g.natDegree*g.leadingCoeff*g.discr) *
        (-1:ℂ)^(f.natDegree*g.natDegree) *
        Polynomial.resultant f g f.natDegree g.natDegree ^ 2) := by convert hh using 1; ring
    _ = _ := by ring

theorem discr_ne_zero_of_separable (f : Polynomial ℂ)
    (hf : 0 < f.natDegree) (hsep : f.Separable) : f.discr ≠ 0 := by
  have hres : Polynomial.resultant f f.derivative f.natDegree (f.natDegree-1) ≠ 0 := by
    simpa only [natDegree_derivative] using Polynomial.resultant_ne_zero f f.derivative hsep
  rw [Polynomial.resultant_deriv (by rwa [← natDegree_pos_iff_degree_pos])] at hres
  intro hd
  exact hres (by rw [hd,mul_zero])

#assert_trust kernel resultant_product_derivative
#assert_trust kernel discr_mul_with_sign
#assert_trust kernel discr_ne_zero_of_separable
#print axioms discr_mul_with_sign
end NLA.Proofs.TR26.BinaryDiscriminant
