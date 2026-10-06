/-
Fixed-row Gaussian base case for the spectral recursion. Exact numerical and
probability contracts were independently approved before implementation in
reviews/spectral-recursion-specification.md.
-/
import NLA.IE06.GaussianOvercrowding
import NLA.IE06.GaussianPivotConditioning
import NLA.IE06.SpectralRecursionScalars

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal
namespace NLA.IE06.GaussianSpectralBase
open GaussianNull GaussianPivotConditioning Spectral ScalarRecurrence SpectralRecursionScalars

/-- The actual selected original-row square block at a canonical pivot stage. -/
def block {n t : ℕ} (ht : t≤n) (A : Mat n) : Mat t :=
  selectedBlock ht (pivotOrder ht A) A

theorem fixed_block_measurePreserving {n t : ℕ} (ht : t≤n) (π : Fin t ↪ Fin n) :
    MeasurePreserving (selectedBlock ht π) (gaussianMatrix n) (gaussianRect t t) := by
  have hp : MeasurePreserving (prefixRows ht) (gaussianMatrix n) (gaussianRect n t) :=
    ⟨by unfold prefixRows; fun_prop, gaussian_prefixRows_map ht⟩
  exact (GaussianOvercrowding.restrictRows_measurePreserving π π.injective).comp hp

theorem card_rowOrders_le (n t : ℕ) [Fintype (Fin t ↪ Fin n)] : Fintype.card (Fin t ↪ Fin n)≤n^t := by
  simpa only [Fintype.card_fun,Fintype.card_fin] using
    Fintype.card_le_of_injective (fun π : Fin t ↪ Fin n => (π : Fin t → Fin n))
      Function.Embedding.coe_injective

theorem fixed_block_tail {n t d : ℕ} (ht : t≤n) (π : Fin t ↪ Fin n)
    (hd : 4≤d) (hdt : d<t) {θ : ℝ} (hθ : 0<θ) (hθ1 : θ≤1) :
    gaussianMatrix n {A | singularValue (selectedBlock ht π A) (t-d-1)≤
      (d:ℝ)*θ/(4*Real.exp 1*Real.sqrt t)} ≤
      ENNReal.ofReal ((t:ℝ)^(d+1)*θ^((d:ℝ)^2/4)) := by
  have hmp := fixed_block_measurePreserving ht π
  apply (Measure.le_map_apply hmp.measurable.aemeasurable
    {H : RectMat t t | singularValue (Matrix.of H) (t-d-1)≤
      (d:ℝ)*θ/(4*Real.exp 1*Real.sqrt t)}).trans
  rw [hmp.map_eq]
  exact GaussianOvercrowding.gaussian_overcrowding hd hdt hθ hθ1

theorem measure_finite_iUnion_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (E : ι → Set Ω) (b : ℝ≥0∞) (h : ∀ i, μ (E i)≤b) :
    μ (⋃ i, E i)≤(Fintype.card ι:ℝ≥0∞)*b := by
  calc
    _ ≤ ∑ i, μ (E i) := by simpa only [tsum_fintype] using measure_iUnion_le (μ:=μ) E
    _ ≤ ∑ _i : ι, b := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp

theorem rowOrder_union_le {n t : ℕ} (E : (Fin t ↪ Fin n) → Set (Mat n))
    {b : ℝ} (_hb : 0≤b) (h : ∀ π, gaussianMatrix n (E π)≤ENNReal.ofReal b) :
    gaussianMatrix n (⋃ π, E π)≤ENNReal.ofReal ((n:ℝ)^t*b) := by
  calc
    _ ≤ (Fintype.card (Fin t ↪ Fin n):ℝ≥0∞)*ENNReal.ofReal b :=
      measure_finite_iUnion_le _ _ _ h
    _ ≤ (n:ℝ≥0∞)^t*ENNReal.ofReal b := by
      gcongr
      exact_mod_cast card_rowOrders_le n t
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (Nat.cast_nonneg n),
        ENNReal.ofReal_natCast]

theorem adaptive_rowOrder_union_le {n t : ℕ} (order : Mat n → (Fin t ↪ Fin n))
    (E : (Fin t ↪ Fin n) → Set (Mat n)) {b : ℝ} (hb : 0≤b)
    (h : ∀ π, gaussianMatrix n (E π)≤ENNReal.ofReal b) :
    gaussianMatrix n {A | A∈E (order A)}≤ENNReal.ofReal ((n:ℝ)^t*b) := by
  have hsub : {A : Mat n | A∈E (order A)} ⊆ ⋃ π, E π := by
    intro A hA
    exact Set.mem_iUnion.mpr ⟨order A,hA⟩
  exact (measure_mono hsub).trans (rowOrder_union_le E hb h)

/-- Union over fixed row orders, followed by any adaptive row order. -/
theorem adaptive_block_tail {n t d : ℕ} (ht : t≤n) (order : Mat n → (Fin t ↪ Fin n))
    (hd : 4≤d) (hdt : d<t) {θ : ℝ} (hθ : 0<θ) (hθ1 : θ≤1) :
    gaussianMatrix n {A | singularValue (selectedBlock ht (order A) A) (t-d-1)≤
      (d:ℝ)*θ/(4*Real.exp 1*Real.sqrt t)} ≤
      ENNReal.ofReal ((n:ℝ)^t*(t:ℝ)^(d+1)*θ^((d:ℝ)^2/4)) := by
  have hb : 0≤(t:ℝ)^(d+1)*θ^((d:ℝ)^2/4) :=
    mul_nonneg (pow_nonneg (Nat.cast_nonneg t) _) (Real.rpow_nonneg hθ.le _)
  have hh := adaptive_rowOrder_union_le order
    (fun π => {A | singularValue (selectedBlock ht π A) (t-d-1)≤
      (d:ℝ)*θ/(4*Real.exp 1*Real.sqrt t)}) hb
    (fun π => fixed_block_tail ht π hd hdt hθ hθ1)
  rw [← mul_assoc] at hh
  exact hh

theorem selected_block_tail {n t d : ℕ} (ht : t≤n) (hd : 4≤d) (hdt : d<t)
    {θ : ℝ} (hθ : 0<θ) (hθ1 : θ≤1) :
    gaussianMatrix n {A | singularValue (block ht A) (t-d-1)≤
      (d:ℝ)*θ/(4*Real.exp 1*Real.sqrt t)} ≤
      ENNReal.ofReal ((n:ℝ)^t*(t:ℝ)^(d+1)*θ^((d:ℝ)^2/4)) :=
  adaptive_block_tail ht (pivotOrder ht) hd hdt hθ hθ1

theorem selected_block_profile_base {n t d : ℕ} (ht : t≤n) (hdt : d<t)
    (hlog : 256≤Real.log (n:ℝ)) (hd : ⌈Real.sqrt (Real.log (n:ℝ))⌉₊≤d)
    {β D : ℝ} (hβ : 1≤β) (hD : 4*β+4004≤D)
    (hbase : t≤8*step (Real.log (n:ℝ)) d) :
    gaussianMatrix n {A | singularValue (block ht A) (t-d-1)<
      profile n (Real.log (n:ℝ)) D d} ≤ ENNReal.ofReal (Real.exp (-β*Real.log (n:ℝ))) := by
  have hd16 : 16≤d := (sixteen_le_ceil_sqrt hlog).trans hd
  have hd0 : 0<d := by omega
  have hn : 0<n := lt_of_lt_of_le (lt_trans hd0 hdt) ht
  have hl : 0<Real.log (n:ℝ) := by linarith
  have hD4 : 4≤D := by linarith
  have hg := profile_le_base_threshold hn hd0 hdt ht hl.le hD4
  calc
    _ ≤ gaussianMatrix n {A | singularValue (block ht A) (t-d-1)≤
        (d:ℝ)*baseTheta (Real.log (n:ℝ)) D d/(4*Real.exp 1*Real.sqrt t)} :=
      measure_mono (fun _ h => h.le.trans hg)
    _ ≤ ENNReal.ofReal ((n:ℝ)^t*(t:ℝ)^(d+1)*
        (baseTheta (Real.log (n:ℝ)) D d)^((d:ℝ)^2/4)) :=
      selected_block_tail ht (by omega) hdt (baseTheta_pos _ _ _) (baseTheta_le_one hl.le hD4 d)
    _ ≤ _ := ENNReal.ofReal_le_ofReal (base_union_bound hn hdt ht hd0 hβ hD hl hbase)

#assert_trust kernel block
#print axioms block
#assert_trust kernel fixed_block_measurePreserving
#print axioms fixed_block_measurePreserving
#assert_trust kernel card_rowOrders_le
#print axioms card_rowOrders_le
#assert_trust kernel fixed_block_tail
#print axioms fixed_block_tail
#assert_trust kernel measure_finite_iUnion_le
#print axioms measure_finite_iUnion_le
#assert_trust kernel rowOrder_union_le
#print axioms rowOrder_union_le
#assert_trust kernel adaptive_rowOrder_union_le
#print axioms adaptive_rowOrder_union_le
#assert_trust kernel adaptive_block_tail
#print axioms adaptive_block_tail
#assert_trust kernel selected_block_tail
#print axioms selected_block_tail
#assert_trust kernel selected_block_profile_base
#print axioms selected_block_profile_base
end NLA.IE06.GaussianSpectralBase
