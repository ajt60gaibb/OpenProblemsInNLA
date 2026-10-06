/-
Gaussian overcrowding A3, combining exact inverse principal-minor moments
with the genuine spectral event implication. The complete contract was
independently approved before implementation; see
reviews/gaussian-overcrowding-specification.md.
-/
import NLA.IE06.GaussianPrincipalTail
import NLA.IE06.Spectral
import NLA.IE06.GaussianOvercrowdingSpectral

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators
namespace NLA.IE06.GaussianOvercrowding
open GaussianNull GaussianQuadratic GaussianRegression GaussianPrincipalTail
open GaussianOvercrowdingScalars
local instance matrixBorelSpace (d : ℕ) : BorelSpace (Mat d) :=
  inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))
local instance gaussianRect_probability (m n : ℕ) : IsProbabilityMeasure (gaussianRect m n) := by
  unfold gaussianRect
  infer_instance

def restrictRows {m n p : ℕ} (f : Fin m → Fin n) (G : RectMat n p) : RectMat m p :=
  fun i => G (f i)

theorem restrictRows_measurePreserving {m n p : ℕ} (f : Fin m → Fin n)
    (hf : Function.Injective f) :
    MeasurePreserving (@restrictRows m n p f) (gaussianRect n p) (gaussianRect m p) := by
  have hI : iIndepFun (fun i : Fin n => fun G : RectMat n p => G i) (gaussianRect n p) :=
    iIndepFun_pi (μ := fun _ : Fin n => gaussianVector p) (X := fun _ => id)
      (fun _ => aemeasurable_id)
  have hJ := iIndepFun.precomp hf hI
  refine ⟨by unfold restrictRows; fun_prop, ?_⟩
  have hh := hJ.map_fun_eq_pi_map (fun i => (measurable_pi_apply (f i)).aemeasurable)
  change (gaussianRect n p).map (fun G i => G (f i)) = _
  rw [hh]
  change Measure.pi (fun i : Fin m => (gaussianRect n p).map (Function.eval (f i))) =
    Measure.pi (fun _ : Fin m => gaussianVector p)
  congr 1
  funext i
  exact (measurePreserving_eval (fun _ : Fin n => gaussianVector p) (f i)).map_eq

theorem principalDet_measurable {m n : ℕ} (S : Finset (Fin m)) :
    Measurable (@principalDet m n S) := by
  let : MeasurableSpace (Matrix S S ℝ) := inferInstanceAs (MeasurableSpace (S → S → ℝ))
  let : BorelSpace (Matrix S S ℝ) := inferInstanceAs (BorelSpace (S → S → ℝ))
  have hi : Measurable (fun G : RectMat m n => (gram G)⁻¹) :=
    (measurable_inverse m).comp gram_continuous.measurable
  have hs : Measurable (fun G : RectMat m n =>
      (gram G)⁻¹.submatrix (Subtype.val : S → Fin m) (Subtype.val : S → Fin m)) := by
    exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
      (measurable_pi_apply j.val).comp ((measurable_pi_apply i.val).comp hi)
  exact continuous_id.matrix_det.measurable.comp hs

theorem principal_union_measurable (m n r : ℕ) (a : ℝ) :
    MeasurableSet {G : RectMat m n | ∃ S ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
      a ≤ principalDet S G} := by
  have heq : {G : RectMat m n | ∃ S ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
      a ≤ principalDet S G} =
      ⋃ S ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
        {G : RectMat m n | a ≤ principalDet S G} := by ext G; simp
  rw [heq]
  exact MeasurableSet.iUnion fun S => MeasurableSet.iUnion fun _ =>
    measurableSet_le measurable_const (principalDet_measurable S)

theorem threshold_moment_rewrite (N C t : ℝ) (r q : ℕ) :
    N * C / (((t ^ (2 * r))⁻¹ / N) ^ q) = N * C * N ^ q * t ^ (2 * r * q) := by
  simp only [div_eq_mul_inv, mul_pow, inv_pow, _root_.mul_inv_rev, inv_inv]
  rw [← pow_mul]
  ring

/-- Gaussian overcrowding at the exact source singular-value index and real
theta exponent, with universal threshold constant 1/(4e). -/
theorem gaussian_overcrowding {n j : ℕ} (hj : 4 ≤ j) (hjn : j < n)
    {θ : ℝ} (hθ : 0 < θ) (hθone : θ ≤ 1) :
    gaussianRect n n {G | Spectral.singularValue (Matrix.of G) (n - j - 1) ≤
      (j : ℝ) * θ / (4 * Real.exp 1 * Real.sqrt n)} ≤
      ENNReal.ofReal ((n : ℝ) ^ (j + 1) * θ ^ ((j : ℝ) ^ 2 / 4)) := by
  let q := momentOrder j
  let r := minorSize j
  let m := n - 2 * q
  let N : ℝ := m.choose r
  let t : ℝ := (j : ℝ) * θ / (4 * Real.exp 1 * Real.sqrt n)
  let a : ℝ := (t ^ (2 * r))⁻¹ / N
  obtain ⟨hq, hr, hrm, hdim, _⟩ := dimensions hj hjn
  change 1 ≤ q at hq
  change 1 ≤ r at hr
  change r ≤ m at hrm
  change 2 * q + r = j + 1 at hdim
  have hmn : m ≤ n := Nat.sub_le _ _
  have hmq : m + 2 * q = n := by dsimp [m]; omega
  have hind : m - r = n - j - 1 := by omega
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Nat.choose_pos hrm
  have ht : 0 < t := by
    dsimp [t]
    have hj' : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
    have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    positivity
  have ha : 0 < a := by dsimp [a]; positivity
  let f : Fin m → Fin n := Fin.castLE hmn
  have hf : Function.Injective f := Fin.castLE_injective hmn
  let R : RectMat n n → RectMat m n := restrictRows f
  have hmp : MeasurePreserving R (gaussianRect n n) (gaussianRect m n) :=
    restrictRows_measurePreserving f hf
  have hR : ∀ᵐ G ∂gaussianRect n n, (gram (R G)).PosDef :=
    hmp.quasiMeasurePreserving.ae (gram_posDef_ae m n hmn)
  let A : Set (RectMat m n) := {H | ∃ S ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
    a ≤ principalDet S H}
  have hA : MeasurableSet A := principal_union_measurable m n r a
  have hinc : {G : RectMat n n | Spectral.singularValue (Matrix.of G) (n - j - 1) ≤ t}
      ≤ᵐ[gaussianRect n n] R ⁻¹' A := by
    filter_upwards [hR] with G hG
    intro hsmall
    have hrow := GaussianOvercrowdingSpectral.singularValue_rows_le
      (Matrix.of G) ⟨f, hf⟩ ⟨m - r, by omega⟩
    have hs : Spectral.singularValue (Matrix.of (R G)) (m - r) ≤ t := by
      calc
        _ ≤ Spectral.singularValue (Matrix.of G) (m - r) := hrow
        _ = Spectral.singularValue (Matrix.of G) (n - j - 1) := by rw [hind]
        _ ≤ t := hsmall
    obtain ⟨S, hS, hlarge⟩ :=
      GaussianOvercrowdingSpectral.singular_event_implies_large_inverse_gram_minor
        (Matrix.of (R G)) hG hr hrm hmn ht hs
    exact ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hS⟩, hlarge⟩
  change gaussianRect n n {G | Spectral.singularValue (Matrix.of G) (n - j - 1) ≤ t} ≤ _
  calc
    _ ≤ gaussianRect n n (R ⁻¹' A) := measure_mono_ae hinc
    _ = gaussianRect m n A := by rw [← hmp.map_eq, Measure.map_apply hmp.measurable hA]
    _ ≤ ENNReal.ofReal (N * (Real.exp 1 / q) ^ (r * q) / a ^ q) :=
      principal_union_tail hq hrm hmq.le ha
    _ = ENNReal.ofReal (N * (Real.exp 1 / q) ^ (r * q) * N ^ q * t ^ (2 * r * q)) := by
      dsimp only [a]
      rw [threshold_moment_rewrite]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (overcrowding_scalar hj hjn hθ hθone)

#assert_trust kernel restrictRows
#assert_trust kernel restrictRows_measurePreserving
#assert_trust kernel principalDet_measurable
#assert_trust kernel principal_union_measurable
#assert_trust kernel threshold_moment_rewrite
#assert_trust kernel gaussian_overcrowding
#print axioms gaussian_overcrowding
end NLA.IE06.GaussianOvercrowding
