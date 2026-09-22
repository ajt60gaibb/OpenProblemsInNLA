/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Original counterexample and mathematical proof: Matthew J. Colbrook.
AI-assisted affine/projective closure bridge; no complete verification is claimed.
-/
import NLA.TR27.Semantics

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct LinearAlgebra.Projectivization
namespace NLA.TR27
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem coneRankAtMost_smul (C : Set W) (r : ℕ) (w : W)
    (hw : ConeRankAtMost C r w) (a : ℂ) : ConeRankAtMost C r (a • w) := by
  obtain ⟨k, hk, b, x, hx, heq⟩ := hw
  refine ⟨k, hk, fun i => a * b i, x, hx, ?_⟩
  simp only [heq, Finset.smul_sum, smul_smul]

/-- Every homogeneous component vanishes on a scalar-closed set whenever the
whole polynomial does. This uses all complex scalar parameters. -/
theorem homogeneousComponent_vanishes {σ : Type*}
    (D : Set (σ → ℂ)) (hD : ∀ (a : ℂ) w, w ∈ D → a • w ∈ D)
    (f : MvPolynomial σ ℂ) (hf : ∀ w ∈ D, MvPolynomial.eval w f = 0)
    (d : ℕ) (v : σ → ℂ) (hv : v ∈ D) :
    MvPolynomial.eval v (MvPolynomial.homogeneousComponent d f) = 0 := by
  classical
  let P : Polynomial ℂ := ∑ n ∈ Finset.range (f.totalDegree + 1),
    Polynomial.C (MvPolynomial.eval v (MvPolynomial.homogeneousComponent n f)) * Polynomial.X ^ n
  have heval (a : ℂ) : P.eval a = MvPolynomial.eval (a • v) f := by
    dsimp [P]
    conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent f]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, map_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [homogeneous_eval_smul _ n (MvPolynomial.homogeneousComponent_mem n f), mul_comm]
  have hP : P = 0 := Polynomial.funext fun a => by
    rw [heval, hf (a • v) (hD a v hv), Polynomial.eval_zero]
  by_cases hd : d < f.totalDegree + 1
  · have h := congrArg (fun p : Polynomial ℂ => p.coeff d) hP
    simpa [P, Polynomial.coeff_sum, Polynomial.coeff_C_mul_X_pow, hd] using h
  · have hdeg : f.totalDegree < d := by omega
    rw [MvPolynomial.homogeneousComponent_eq_zero d f hdeg, map_zero]

theorem homogeneous_eval_rep_iff (X : ProjectiveVariety W) (v : W) (hv : v ≠ 0)
    (f : MvPolynomial (Fin X.dimension) ℂ) (d : ℕ) (hf : f.IsHomogeneous d) :
    MvPolynomial.eval (X.coordinates (Projectivization.mk ℂ v hv).rep) f = 0 ↔
      MvPolynomial.eval (X.coordinates v) f = 0 := by
  obtain ⟨a, ha, heq⟩ := represents_mk v hv
  rw [heq, map_smul, homogeneous_eval_smul f d hf]
  simp [mul_eq_zero, pow_ne_zero d ha]


theorem projective_affine_border (X : ProjectiveVariety W) (hX : X.Admissible)
    (r : ℕ) (v : W) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈
        X.zariskiClosure {q | ProjectiveRankAtMost X.points r q} ↔
      v ∈ X.affineClosure {w | ConeRankAtMost X.cone r w} := by
  classical
  constructor
  · intro hp f hf
    have hvan := MvPolynomial.mem_vanishingIdeal_iff.mp hf
    change MvPolynomial.eval (X.coordinates v) f = 0
    rw [← MvPolynomial.sum_homogeneousComponent f, map_sum]
    apply Finset.sum_eq_zero
    intro d _
    apply (homogeneous_eval_rep_iff X v hv _ d (MvPolynomial.homogeneousComponent_mem d f)).mp
    apply hp _ d (MvPolynomial.homogeneousComponent_mem d f)
    intro q hq
    refine homogeneousComponent_vanishes
      (X.coordinates '' {w | ConeRankAtMost X.cone r w}) ?_ f hvan d _ ?_
    · rintro a _ ⟨w, hw, rfl⟩
      exact ⟨a • w, coneRankAtMost_smul X.cone r w hw a, map_smul X.coordinates a w⟩
    · refine ⟨q.rep, ?_, rfl⟩
      apply (projective_cone_rank X hX r q.rep q.rep_nonzero).mp
      simpa using hq
  · intro hvcl f d hf hY
    apply (homogeneous_eval_rep_iff X v hv f d hf).mpr
    have hcv : X.coordinates v ≠ 0 := X.coordinates.map_ne_zero_iff.mpr hv
    obtain ⟨j, hj⟩ : ∃ j, X.coordinates v j ≠ 0 := by
      by_contra h
      push Not at h
      exact hcv (funext h)
    let g := MvPolynomial.X j * f
    have hg : g ∈ MvPolynomial.vanishingIdeal ℂ
        (X.coordinates '' {w | ConeRankAtMost X.cone r w}) := by
      apply MvPolynomial.mem_vanishingIdeal_iff.mpr
      rintro _ ⟨w, hw, rfl⟩
      change MvPolynomial.eval (X.coordinates w) g = 0
      by_cases hwz : w = 0
      · simp [g, hwz]
      · have hq := (projective_cone_rank X hX r w hwz).mpr hw
        have heval := (homogeneous_eval_rep_iff X w hwz f d hf).mp
          (hY (Projectivization.mk ℂ w hwz) hq)
        simp [g, heval]
    have h := hvcl g hg
    change MvPolynomial.eval (X.coordinates v) g = 0 at h
    simp only [g, map_mul, MvPolynomial.eval_X] at h
    exact (mul_eq_zero.mp h).resolve_left hj

#print axioms projective_affine_border
#print axioms homogeneousComponent_vanishes
end NLA.TR27
