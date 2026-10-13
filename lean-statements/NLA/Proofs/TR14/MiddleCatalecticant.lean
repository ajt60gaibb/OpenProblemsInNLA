import NLA.Proofs.TR14.FrobeniusMinimal
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
The exact middle Hankel catalecticant has rank equal to the least apolar
degree in a monic affine chart. Projective chart transport back to arbitrary
original moments is a separate obligation.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Polynomial

namespace NLA.Proofs.TR14

/-- The source's zero-based middle Hankel matrix, with all indices in the
original moment range `0,…,D`. -/
noncomputable def middleCatalecticant {D : ℕ} (h : Fin (D + 1) → ℂ) :
    Matrix (Fin (D / 2 + 1)) (Fin ((D + 1) / 2 + 1)) ℂ :=
  fun i j => h ⟨i.val + j.val, by
    have hi := i.isLt
    have hj := j.isLt
    omega⟩

private noncomputable def powerQuotientMap (g : Polynomial ℂ) (s : ℕ) :
    (Fin (s + 1) → ℂ) →ₗ[ℂ] AdjoinRoot g :=
  Fintype.linearCombination ℂ
    (fun j : Fin (s + 1) => (AdjoinRoot.root g) ^ j.val)

private theorem powerQuotientMap_surjective (g : Polynomial ℂ) (hg : g.Monic)
    (s : ℕ) (hs : g.natDegree ≤ s + 1) :
    Function.Surjective (powerQuotientMap g s) := by
  let b := (AdjoinRoot.powerBasis' hg).basis
  have hspan : Submodule.span ℂ
      (Set.range (fun j : Fin (s + 1) => (AdjoinRoot.root g) ^ j.val)) = ⊤ := by
    apply eq_top_iff.mpr
    calc
      (⊤ : Submodule ℂ (AdjoinRoot g)) =
          Submodule.span ℂ (Set.range b) := b.span_eq.symm
      _ ≤ Submodule.span ℂ
          (Set.range (fun j : Fin (s + 1) => (AdjoinRoot.root g) ^ j.val)) := by
        apply Submodule.span_mono
        intro x hx
        obtain ⟨i, rfl⟩ := hx
        refine ⟨⟨i.val, by
          have hi : i.val < g.natDegree := by simpa using i.isLt
          omega⟩, ?_⟩
        simp [b, (AdjoinRoot.powerBasis' hg).basis_eq_pow i]
  exact (span_range_eq_top_iff_surjective_fintypeLinearCombination ℂ
    (fun j : Fin (s + 1) => (AdjoinRoot.root g) ^ j.val)).mp hspan

private noncomputable def quotientRowMap {D : ℕ}
    (h : Fin (D + 1) → ℂ) (g : Polynomial ℂ)
    (hg : g.Monic) (hrD : g.natDegree ≤ D) :
    AdjoinRoot g →ₗ[ℂ] (Fin (D / 2 + 1) → ℂ) where
  toFun x i := quotientMomentFunctional h g hg hrD
    ((AdjoinRoot.root g) ^ i.val * x)
  map_add' := by
    intro x y
    funext i
    simp [mul_add]
  map_smul' := by
    intro c x
    funext i
    simp

/-- In a monic least-apolar chart, the actual rectangular middle Hankel
matrix has rank the exact least homogeneous apolar degree. -/
theorem middleCatalecticant_rank_normalized {D : ℕ}
    (h : Fin (D + 1) → ℂ) (hh : h ≠ 0) (g : Polynomial ℂ)
    (hg : g.Monic) (hrPos : 1 ≤ g.natDegree)
    (hrHi : g.natDegree ≤ D / 2 + 1)
    (hrD : g.natDegree ≤ D)
    (hAp : IsApolar h g.natDegree hrD
      (fun i : Fin (g.natDegree + 1) => g.coeff i.val))
    (hmin : ∀ d : ℕ, ∀ hd : d ≤ D, d < g.natDegree →
      ∀ b : Fin (d + 1) → ℂ, IsApolar h d hd b → b = 0) :
    (middleCatalecticant h).rank = g.natDegree := by
  classical
  let t : AdjoinRoot g := AdjoinRoot.root g
  let Λ := quotientMomentFunctional h g hg hrD
  let Φ := quotientRowMap h g hg hrD
  let ρa := powerQuotientMap g (D / 2)
  let ρb := powerQuotientMap g ((D + 1) / 2)
  have hρa : Function.Surjective ρa :=
    powerQuotientMap_surjective g hg (D / 2) hrHi
  have hρb : Function.Surjective ρb :=
    powerQuotientMap_surjective g hg ((D + 1) / 2) (by omega)
  have hrec : MonicMomentRecurrence h g :=
    monicMomentRecurrence_of_apolar h g hg hrD hAp
  have hall := quotientMomentFunctional_all h g hg hrD hrec
  have hFrob := quotientMomentFunctional_frobenius h hh g hg hrPos hrD hAp hmin
  have hΦinj : Function.Injective Φ := by
    intro x y hxy
    have hx0 : Φ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hzero : x - y = 0 := hFrob (x - y) (by
    intro z
    obtain ⟨c, rfl⟩ := hρa z
    have hs : Λ ((x - y) * ρa c) =
        ∑ i : Fin (D / 2 + 1), c i * Φ (x - y) i := by
      change Λ ((x - y) * ∑ i : Fin (D / 2 + 1), c i • t ^ i.val) =
        ∑ i : Fin (D / 2 + 1), c i * Λ (t ^ i.val * (x - y))
      rw [Finset.mul_sum, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm (x - y)]
    rw [hs]
    simp [congrFun hx0])
    exact sub_eq_zero.mp hzero
  have hfactor : (middleCatalecticant h).mulVecLin = Φ.comp ρb := by
    apply LinearMap.ext
    intro c
    funext i
    have hsum : Λ (t ^ i.val * ρb c) =
        ∑ j : Fin ((D + 1) / 2 + 1),
          h ⟨i.val + j.val, by have hi := i.isLt; have hj := j.isLt; omega⟩ * c j := by
      change Λ (t ^ i.val * ∑ j : Fin ((D + 1) / 2 + 1), c j • t ^ j.val) = _
      rw [Finset.mul_sum, map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_smul_comm, map_smul, smul_eq_mul]
      have hp : t ^ i.val * t ^ j.val = t ^ (i.val + j.val) := by rw [pow_add]
      rw [hp, hall ⟨i.val + j.val, by have hi := i.isLt; have hj := j.isLt; omega⟩]
      ring
    change (∑ j : Fin ((D + 1) / 2 + 1),
      h ⟨i.val + j.val, by have hi := i.isLt; have hj := j.isLt; omega⟩ * c j) =
        Λ (t ^ i.val * ρb c)
    exact hsum.symm
  rw [Matrix.rank, hfactor, LinearMap.range_comp]
  have hρbRange : LinearMap.range ρb = ⊤ := LinearMap.range_eq_top.mpr hρb
  rw [hρbRange, Submodule.map_top]
  exact (LinearMap.finrank_range_of_inj hΦinj).trans (quotient_finrank g hg)

#assert_trust kernel middleCatalecticant
#assert_trust kernel middleCatalecticant_rank_normalized
#print axioms middleCatalecticant_rank_normalized

end NLA.Proofs.TR14
