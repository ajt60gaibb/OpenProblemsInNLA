import ProofProject.SourcePieceError
import ProofProject.SourceSeparatorScale
import ProofProject.FiniteGeometricError

/-!
# Actual commuting separators for retained source pieces

A gap of two at the cut suffices. In particular an increasing family of one
parity has the required gap. The raw square-root error decreases doubly
exponentially with the first retained original index, uniformly in time.
-/

noncomputable section

namespace ProofProject

open Finset

theorem sum_sourceSeparator_deleted_le {ι : Type*} (s : Finset ι) (q : ι → ℕ)
    (hq : Set.InjOn q (s : Set ι)) (k : ℕ) (hside : ∀ j ∈ s, q j ≤ k) :
    (∑ j ∈ s, Real.sqrt (sourceSeparatorRate k / sourcePieceLambda (q j + 1))) ≤
      8 * sourceSeparatorDecay k := by
  have hinj : Set.InjOn (fun j => k - q j) (s : Set ι) := by
    intro i hi j hj hij
    dsimp only at hij
    exact hq hi hj (by have := hside i hi; have := hside j hj; omega)
  have hgeom := sum_geometric_injOn_le s (fun j => k - q j) hinj
    (by norm_num : (0 : ℝ) ≤ 7 / 8) (by norm_num : (7 / 8 : ℝ) < 1)
  norm_num at hgeom
  calc
    _ ≤ ∑ j ∈ s, sourceSeparatorDecay k * (7 / 8 : ℝ) ^ (k - q j) :=
      sum_le_sum fun j hj => sourceSeparatorRate_deleted_le (hside j hj)
    _ = sourceSeparatorDecay k * ∑ j ∈ s, (7 / 8 : ℝ) ^ (k - q j) := by rw [mul_sum]
    _ ≤ sourceSeparatorDecay k * 8 := mul_le_mul_of_nonneg_left hgeom (sourceSeparatorDecay_nonneg k)
    _ = _ := by ring

theorem sum_sourceSeparator_retained_le {ι : Type*} (s : Finset ι) (q : ι → ℕ)
    (hq : Set.InjOn q (s : Set ι)) (k : ℕ) (hside : ∀ j ∈ s, k + 2 ≤ q j) :
    (∑ j ∈ s, Real.sqrt (sourcePieceLambda (q j) / sourceSeparatorRate k)) ≤
      8 * sourceSeparatorDecay k := by
  have hinj : Set.InjOn (fun j => q j - (k + 2)) (s : Set ι) := by
    intro i hi j hj hij
    dsimp only at hij
    exact hq hi hj (by have := hside i hi; have := hside j hj; omega)
  have hgeom := sum_geometric_injOn_le s (fun j => q j - (k + 2)) hinj
    (by norm_num : (0 : ℝ) ≤ 7 / 8) (by norm_num : (7 / 8 : ℝ) < 1)
  norm_num at hgeom
  calc
    _ ≤ ∑ j ∈ s, sourceSeparatorDecay k * (7 / 8 : ℝ) ^ (q j - (k + 2)) :=
      sum_le_sum fun j hj => sourceSeparatorRate_retained_le (hside j hj)
    _ = sourceSeparatorDecay k * ∑ j ∈ s, (7 / 8 : ℝ) ^ (q j - (k + 2)) := by rw [mul_sum]
    _ ≤ sourceSeparatorDecay k * 8 := mul_le_mul_of_nonneg_left hgeom (sourceSeparatorDecay_nonneg k)
    _ = _ := by ring

theorem sum_sourcePiece_remainder_le {ι : Type*} (s : Finset ι) (q : ι → ℕ)
    (hq : Set.InjOn q (s : Set ι)) (J : ℕ) (hside : ∀ j ∈ s, J ≤ q j) :
    (∑ j ∈ s, sourcePieceScale (q j) ^ (-1 / 8 : ℝ)) ≤
      16 * sourcePieceScale J ^ (-1 / 8 : ℝ) := by
  have hinj : Set.InjOn (fun j => q j - J) (s : Set ι) := by
    intro i hi j hj hij
    dsimp only at hij
    exact hq hi hj (by have := hside i hi; have := hside j hj; omega)
  have hgeom := sum_geometric_injOn_le s (fun j => q j - J) hinj
    (by norm_num : (0 : ℝ) ≤ 15 / 16) (by norm_num : (15 / 16 : ℝ) < 1)
  norm_num at hgeom
  calc
    _ ≤ ∑ j ∈ s, (15 / 16 : ℝ) ^ (q j - J) * sourcePieceScale J ^ (-1 / 8 : ℝ) :=
      sum_le_sum fun j hj => sourcePieceScale_neg_eighth_geometric_le (hside j hj)
    _ = (∑ j ∈ s, (15 / 16 : ℝ) ^ (q j - J)) * sourcePieceScale J ^ (-1 / 8 : ℝ) := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hgeom (Real.rpow_nonneg (sourcePieceScale_pos J).le _)

universe u

/-- The actual source separators have a uniform raw square-root error bound.
The normalized budget uses this error multiplied by `sqrt (M+1)`. -/
theorem exists_sourcePiece_separators :
    ∀ M : ℝ, 1 ≤ M → ∃ C : ℝ, 0 < C ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (S : BoundedSemigroup M H) (n : ℕ) (q : Fin n → ℕ),
      (∀ i j, i < j → q i + 2 ≤ q j) →
      ∀ J : ℕ, (∀ j, J ≤ q j) → ∀ t : ℝ, 0 < t →
      ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      ∀ k : ℕ, 0 < k → k < n → ∃ R : H →L[ℂ] H,
        ‖R‖ ≤ M ∧ (∀ j, Commute R (S.sourcePieceOperator (q j) t σ)) ∧
        sqrtSeparationError (fun j => S.sourcePieceOperator (q j) t σ) R k ≤
          C * sourceSeparatorDecay J := by
  intro M hM
  obtain ⟨C, hC, hres⟩ := exists_sourcePieceResolvent_bounds.{u} M hM
  refine ⟨32 * Real.sqrt C, by positivity, ?_⟩
  intro H _ _ _ S n q hgap J hJ t ht σ hσ k hk0 hkn
  classical
  have hmono : StrictMono q := by intro i j hij; have := hgap i j hij; omega
  let last : Fin n := ⟨k - 1, by omega⟩
  let K := q last
  have hJK : J ≤ K := hJ last
  have hdel : ∀ j : Fin n, j.val < k → q j ≤ K := by
    intro j hj
    exact hmono.monotone (show j ≤ last by change j.val ≤ k - 1; omega)
  have hkeep : ∀ j : Fin n, k ≤ j.val → K + 2 ≤ q j := by
    intro j hj
    exact hgap last j (show last < j by change k - 1 < j.val; omega)
  let r := sourceSeparatorRate K
  have hr : 0 < r := sourceSeparatorRate_pos K
  let R := S.resolventAverage r hr
  refine ⟨R, S.resolventAverage_norm_le r hr,
    (fun j => S.resolventAverage_sourcePieceOperator_commute r hr (q j) t σ), ?_⟩
  have h := sourcePiece_sqrtSeparationError_le hC.le ht hr q
    (fun j => S.sourcePieceOperator (q j) t σ) R k
    (fun j _ => (hres H S (q j) t ht σ hσ r hr).1)
    (fun j _ => (hres H S (q j) t ht σ hσ r hr).2)
  have hd := sum_sourceSeparator_deleted_le (univ.filter (fun j : Fin n => j.val < k))
    q hmono.injective.injOn K (fun j hj => hdel j (mem_filter.mp hj).2)
  have hk := sum_sourceSeparator_retained_le (univ.filter (fun j : Fin n => k ≤ j.val))
    q hmono.injective.injOn K (fun j hj => hkeep j (mem_filter.mp hj).2)
  have he := sum_sourcePiece_remainder_le (univ.filter (fun j : Fin n => j.val < k))
    q hmono.injective.injOn J (fun j _ => hJ j)
  have hdec := sourceSeparatorDecay_antitone hJK
  have hrem := sourcePieceScale_neg_eighth_le_separatorDecay J
  apply h.trans
  calc
    _ ≤ Real.sqrt C * (8 * sourceSeparatorDecay K + 8 * sourceSeparatorDecay K +
        16 * sourcePieceScale J ^ (-1 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hd hk) he) (Real.sqrt_nonneg C)
    _ ≤ Real.sqrt C * (32 * sourceSeparatorDecay J) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg C)
      linarith
    _ = _ := by ring

end ProofProject
