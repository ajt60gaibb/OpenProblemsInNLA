import NLA.TR07.DeletionDefect
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Simultaneous reconstruction witnesses

Rank-nullity and Bessel's inequality convert many approximations sharing one
reservoir into a lower bound for deletion deficiency. No bound on the size
of the reconstruction coefficients is needed.
-/

noncomputable section
open scoped BigOperators

namespace NLA.TR07

variable {ι κ δ : Type*} [Fintype ι] [Fintype κ] [Fintype δ]

/-- Restrict a coefficient vector to a finite set of its coordinates. -/
def restrictCoords (D : Finset ι) : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ D where
  toFun x := WithLp.toLp 2 (fun i => x i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype ι] in
@[simp] theorem restrictCoords_apply (D : Finset ι) (x : EuclideanSpace ℝ ι) (i : D) :
    restrictCoords D x i = x i := rfl

theorem sum_norm_sq_orthonormal_le {k : ℕ}
    (B : EuclideanSpace ℝ ι →ₗ[ℝ] Vec k) (w : δ → EuclideanSpace ℝ ι)
    (hw : Orthonormal ℝ w) :
    ∑ j, ‖B (w j)‖ ^ 2 ≤ ∑ i, ‖B (EuclideanSpace.basisFun ι ℝ i)‖ ^ 2 := by
  classical
  have hinner (j : δ) (i : Fin k) :
      inner ℝ (w j) (B.adjoint (EuclideanSpace.basisFun (Fin k) ℝ i)) = B (w j) i := by
    rw [B.adjoint_inner_right, EuclideanSpace.inner_basisFun_real]
  have hcoord (j : ι) (i : Fin k) :
      B.adjoint (EuclideanSpace.basisFun (Fin k) ℝ i) j =
        B (EuclideanSpace.basisFun ι ℝ j) i := by
    rw [← EuclideanSpace.basisFun_inner, B.adjoint_inner_right,
      EuclideanSpace.inner_basisFun_real]
  have hb (i : Fin k) :
      ∑ j, (B (w j) i) ^ 2 ≤ ‖B.adjoint (EuclideanSpace.basisFun (Fin k) ℝ i)‖ ^ 2 := by
    simpa only [hinner, Real.norm_eq_abs, sq_abs] using
      hw.sum_inner_products_le (s := Finset.univ) (B.adjoint (EuclideanSpace.basisFun (Fin k) ℝ i))
  calc
    ∑ j, ‖B (w j)‖ ^ 2 = ∑ i : Fin k, ∑ j, (B (w j) i) ^ 2 := by
      simp_rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.sum_comm
    _ ≤ ∑ i : Fin k, ‖B.adjoint (EuclideanSpace.basisFun (Fin k) ℝ i)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => hb i
    _ = ∑ j, ‖B (EuclideanSpace.basisFun ι ℝ j)‖ ^ 2 := by
      simp_rw [EuclideanSpace.real_norm_sq_eq, hcoord]
      exact Finset.sum_comm

/-- A full collection of dependence vectors with an isometric center block
forces many deletions. The weaker factor one-half suffices for the probability
argument; the displayed error bound actually gives a factor three-quarters. -/
theorem defect_ge_half_of_witnesses {k : ℕ} (a : ι → Vec k) {η : ℝ} (hη : 0 < η)
    (V : EuclideanSpace ℝ κ →ₗ[ℝ] EuclideanSpace ℝ ι)
    (hV : ∀ x, ‖x‖ ≤ ‖V x‖)
    (herror : ∑ j, ‖synthesis a (V (EuclideanSpace.basisFun κ ℝ j))‖ ^ 2 ≤
      (Fintype.card κ : ℝ) * η ^ 2 / 4) :
    (Fintype.card κ : ℝ) / 2 ≤ defect a η := by
  classical
  obtain ⟨D, hD, hgood⟩ := exists_optimal_deletion a η
  let f := (restrictCoords D).comp V
  let K := LinearMap.ker f
  let b := stdOrthonormalBasis ℝ K
  let w : Fin (Module.finrank ℝ K) → EuclideanSpace ℝ κ := fun j => (b j : EuclideanSpace ℝ κ)
  have hw : Orthonormal ℝ w := K.subtypeₗᵢ.orthonormal_comp_iff.mpr b.orthonormal
  have hdim : Fintype.card κ ≤ D.card + Module.finrank ℝ K := by
    have hrank := f.finrank_range_add_finrank_ker
    have hle := (LinearMap.range f).finrank_le
    simp only [finrank_euclideanSpace, Fintype.card_coe] at hrank hle
    dsimp [K]
    omega
  have hbound (j : Fin (Module.finrank ℝ K)) : η ≤ ‖synthesis a (V (w j))‖ := by
    have hnorm : ‖w j‖ = 1 := by exact b.orthonormal.1 j
    have hk : f (w j) = 0 := (b j).property
    have hs : ∀ i, i ∉ Dᶜ → V (w j) i = 0 := by
      intro i hi
      have hiD : i ∈ D := by simpa using hi
      have he := congrArg (fun x : EuclideanSpace ℝ D => x ⟨i, hiD⟩) hk
      simpa [f] using he
    calc
      η = η * ‖w j‖ := by rw [hnorm, mul_one]
      _ ≤ η * ‖V (w j)‖ := mul_le_mul_of_nonneg_left (hV _) hη.le
      _ ≤ ‖synthesis a (V (w j))‖ := hgood _ hs
  have hsquare : (Module.finrank ℝ K : ℝ) * η ^ 2 ≤
      ∑ j, ‖synthesis a (V (w j))‖ ^ 2 := by
    calc
      _ = ∑ _j : Fin (Module.finrank ℝ K), η ^ 2 := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => pow_le_pow_left₀ hη.le (hbound j) 2
  have hhs := sum_norm_sq_orthonormal_le ((synthesis a).comp V) w hw
  simp only [LinearMap.comp_apply] at hhs
  have hdreal : (Fintype.card κ : ℝ) ≤ (D.card : ℝ) + Module.finrank ℝ K := by
    exact_mod_cast hdim
  rw [hD] at hdreal
  have hnormtot := le_trans hsquare (le_trans hhs herror)
  have heta2 : 0 < η ^ 2 := sq_pos_of_pos hη
  nlinarith

end NLA.TR07
