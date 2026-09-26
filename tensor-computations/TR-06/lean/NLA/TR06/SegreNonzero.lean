/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original TR-06 mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.SegreCoordinates
import Mathlib.Algebra.MvPolynomial.Funext

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.TR06.Segre
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

/-- A purely algebraic existence principle, also for an empty variable type. -/
theorem exists_eval_ne_zero {σ : Type*} (p : MvPolynomial σ ℂ) (hp : p ≠ 0) :
    ∃ x : σ → ℂ, MvPolynomial.eval x p ≠ 0 := by
  by_contra! h
  apply hp
  apply MvPolynomial.funext
  intro x
  simpa only [map_zero] using h x

/-- The real subfield is polynomially dense in complex coordinate space.
This proves existence only and uses no measure or dimension argument. -/
theorem exists_real_eval_ne_zero {σ : Type*} (p : MvPolynomial σ ℂ) (hp : p ≠ 0) :
    ∃ x : σ → ℝ, MvPolynomial.eval (fun i => (x i : ℂ)) p ≠ 0 := by
  by_contra! h
  apply hp
  have hrange : (Set.range (Complex.ofReal : ℝ → ℂ)).Infinite :=
    Set.infinite_range_of_injective Complex.ofReal_injective
  apply MvPolynomial.funext_set (fun _ : σ => Set.range (Complex.ofReal : ℝ → ℂ))
    (fun _ => hrange)
  intro x hx
  choose y hy using fun i => hx i (Set.mem_univ i)
  have hxy : x = fun i => (y i : ℂ) := funext (fun i => (hy i).symm)
  rw [hxy, h y, map_zero]

/-- Redundant factors below are used only to exhibit a nonzero evaluation.
All later measure arguments use the exact-dimensional Parameter type. -/
abbrev RawCoordinate (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :=
  (_i : Fin r) × (j : Fin d) × Fin (n j)

def rawFactors (x : RawCoordinate d n r → ℂ) (i : Fin r) (j : Fin d)
    (v : Fin (n j)) : ℂ := x ⟨i, j, v⟩

def rawSumPolynomial (q : TensorIndex d n) : MvPolynomial (RawCoordinate d n r) ℂ :=
  ∑ i : Fin r, ∏ j : Fin d, MvPolynomial.X ⟨i, j, q j⟩

def rawPullback (p : MvPolynomial (TensorIndex d n) ℂ) :
    MvPolynomial (RawCoordinate d n r) ℂ := MvPolynomial.bind₁ rawSumPolynomial p

def rawPivotsPolynomial (q₀ : Fin r → TensorIndex d n) :
    MvPolynomial (RawCoordinate d n r) ℂ :=
  ∏ i : Fin r, ∏ j : Fin d, MvPolynomial.X ⟨i, j, q₀ i j⟩

@[simp] theorem eval_rawSumPolynomial (x : RawCoordinate d n r → ℂ)
    (q : TensorIndex d n) :
    MvPolynomial.eval x (rawSumPolynomial (r := r) q) =
      (∑ i : Fin r, pureTensor (rawFactors x i)) q := by
  simp [rawSumPolynomial, pureTensor, rawFactors]

@[simp] theorem eval_rawPullback (x : RawCoordinate d n r → ℂ)
    (p : MvPolynomial (TensorIndex d n) ℂ) :
    MvPolynomial.eval x (rawPullback (r := r) p) =
      MvPolynomial.eval (fun q => (∑ i, pureTensor (rawFactors x i)) q) p := by
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) x (MvPolynomial.bind₁ rawSumPolynomial p) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  change MvPolynomial.eval (fun q => MvPolynomial.eval x (rawSumPolynomial q)) p = _
  simp only [eval_rawSumPolynomial]

theorem rawPivotsPolynomial_ne_zero (q₀ : Fin r → TensorIndex d n) :
    rawPivotsPolynomial q₀ ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact MvPolynomial.X_ne_zero _

theorem amplitudesPolynomial_ne_zero (q₀ : Fin r → TensorIndex d n) :
    amplitudesPolynomial ℂ q₀ ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => MvPolynomial.X_ne_zero _)

/-- Every prescribed Segre pivot pattern has a nonzero polynomial pullback
whenever p is nonzero at one actual complex decomposition. -/
theorem pullback_ne_zero_of_decomposition (q₀ : Fin r → TensorIndex d n)
    (p : MvPolynomial (TensorIndex d n) ℂ) (A : Tensor ℂ d n)
    (a : Fin r → Tensor ℂ d n) (ha : Decomposes a A)
    (hp : MvPolynomial.eval (fun q => A q) p ≠ 0) : pullback q₀ p ≠ 0 := by
  classical
  choose u hu using fun i => (ha.1 i).2
  let w : RawCoordinate d n r → ℂ := fun t => u t.1 t.2.1 t.2.2
  have hraw : rawPullback (r := r) p ≠ 0 := by
    intro hzero
    have hval : MvPolynomial.eval w (rawPullback (r := r) p) =
        MvPolynomial.eval (fun q => A q) p := by
      rw [eval_rawPullback]
      change MvPolynomial.eval (fun q => (∑ i, pureTensor (u i)) q) p = _
      simp_rw [hu]
      rw [ha.2]
    apply hp
    rw [← hval, hzero, map_zero]
  obtain ⟨x, hx⟩ := exists_eval_ne_zero
    (rawPivotsPolynomial q₀ * rawPullback (r := r) p)
    (mul_ne_zero (rawPivotsPolynomial_ne_zero q₀) hraw)
  rw [map_mul] at hx
  have hxP := (mul_ne_zero_iff.mp hx).1
  have hxR := (mul_ne_zero_iff.mp hx).2
  let b : Fin r → Tensor ℂ d n := fun i => pureTensor (rawFactors x i)
  have hbPivot (i : Fin r) : b i (q₀ i) ≠ 0 := by
    have hprod : (∏ i : Fin r, ∏ j : Fin d, x ⟨i, j, q₀ i j⟩) ≠ 0 := by
      simpa [rawPivotsPolynomial] using hxP
    exact (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
  have hb (i : Fin r) : RankOne (b i) := by
    refine ⟨?_, rawFactors x i, rfl⟩
    intro hzero
    have hz := congrArg (fun B : Tensor ℂ d n => B (q₀ i)) hzero
    exact hbPivot i (by simpa using hz)
  obtain ⟨z, _hzamp, hz⟩ := represented_of_nonzero_pivots q₀ b hb hbPivot
  have hzP : MvPolynomial.eval (fun c => z c) (pullback q₀ p) ≠ 0 := by
    rw [eval_pullback]
    change MvPolynomial.eval (fun q => (∑ i, summands q₀ z i) q) p ≠ 0
    rw [hz]
    exact (eval_rawPullback x p) ▸ hxR
  intro hzero
  exact hzP (by rw [hzero, map_zero])

theorem nonzero_pullback_statement : NonzeroPullbackStatement := by
  intro d n r q₀ p A a ha hp
  have h := pullback_ne_zero_of_decomposition q₀ p A a ha hp
  exact ⟨h, mul_ne_zero (amplitudesPolynomial_ne_zero q₀) h⟩

/-- Scalar extension in the actual Euclidean Segre coordinates. -/
def complexParameter (q₀ : Fin r → TensorIndex d n) (z : Parameter ℝ q₀) : Parameter ℂ q₀ :=
  WithLp.toLp 2 (fun c => (z c : ℂ))

@[simp] theorem factor_complexParameter (q₀ : Fin r → TensorIndex d n)
    (z : Parameter ℝ q₀) (i : Fin r) (j : Fin d) (v : Fin (n j)) :
    factor q₀ (complexParameter q₀ z) i j v = ((factor (𝕜 := ℝ) q₀ z i j v : ℝ) : ℂ) := by
  simp only [factor]
  split_ifs <;> simp [complexParameter]

@[simp] theorem sum_complexParameter (q₀ : Fin r → TensorIndex d n)
    (z : Parameter ℝ q₀) : sum q₀ (complexParameter q₀ z) = complexify (sum q₀ z) := by
  ext q
  simp [sum, summands, pureTensor, complexify]
  simp [complexParameter]

/-- Nonzero complex pullbacks yield actual real decompositions; no assertion
of exact real rank or real identifiability is made here. -/
theorem real_witness_statement : RealWitnessStatement := by
  intro d n r hd q₀ p A a ha hp
  have hnonzero := (nonzero_pullback_statement d n r q₀ p A a ha hp).2
  obtain ⟨x, hx⟩ := exists_real_eval_ne_zero
    (amplitudesPolynomial ℂ q₀ * pullback q₀ p) hnonzero
  rw [map_mul] at hx
  have hxamp := (mul_ne_zero_iff.mp hx).1
  have hxpull := (mul_ne_zero_iff.mp hx).2
  let z : Parameter ℝ q₀ := WithLp.toLp 2 x
  have hzamp (i : Fin r) : z ⟨i, none⟩ ≠ 0 := by
    have hall : (∏ i : Fin r, (x ⟨i, none⟩ : ℂ)) ≠ 0 := by
      simpa [amplitudesPolynomial] using hxamp
    have hi := (Finset.prod_ne_zero_iff.mp hall) i (Finset.mem_univ i)
    exact Complex.ofReal_ne_zero.mp hi
  refine ⟨z, hzamp, decomposes_decoded hd q₀ z hzamp, ?_⟩
  have h := eval_pullback q₀ (complexParameter q₀ z) p
  rw [sum_complexParameter] at h
  exact h ▸ hxpull

#print axioms exists_real_eval_ne_zero
#print axioms nonzero_pullback_statement
#print axioms real_witness_statement
#assert_trust kernel exists_real_eval_ne_zero
#assert_trust kernel nonzero_pullback_statement
#assert_trust kernel real_witness_statement
end NLA.TR06.Segre
