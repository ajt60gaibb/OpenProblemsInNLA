import NLA.Computation.NonadaptiveMatrixQuery
import LeanCert.Tactic.Verification

/-! Finite Gaussian blocks are transported from the exact countable stream
used by the frozen RE-06 program. No alternative sampling law is postulated. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open NLA.Computation.NonadaptiveMatrixQuery

namespace NLA.Proofs.RE06

/-- Every selected coordinate has the original standard real Gaussian law. -/
theorem stream_coordinate_hasLaw (j : ℕ) :
    HasLaw (fun ω : ℕ → ℝ => ω j) (gaussianReal 0 1) GaussianLaw := by
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) j).hasLaw

/-- Injectively selected stream coordinates retain their full joint product law. -/
theorem stream_selection_hasLaw {ι : Type*} (f : ι → ℕ) (hf : Function.Injective f) :
    HasLaw (fun ω : ℕ → ℝ => fun i => ω (f i))
      (Measure.infinitePi (fun _ : ι => gaussianReal 0 1)) GaussianLaw where
  aemeasurable := (measurable_pi_lambda _ (fun i => measurable_pi_apply (f i))).aemeasurable
  map_eq := Measure.map_infinitePi_infinitePi_of_inj hf

/-- The finite version gives the actual finite product used in integrations. -/
theorem finite_stream_selection_hasLaw {ι : Type*} [Fintype ι]
    (f : ι → ℕ) (hf : Function.Injective f) :
    HasLaw (fun ω : ℕ → ℝ => fun i => ω (f i))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) GaussianLaw := by
  simpa only [Measure.infinitePi_eq_pi] using stream_selection_hasLaw f hf

/-- Disjoint groups of selected coordinates have the joint iterated product law. -/
theorem stream_groups_hasLaw {ι : Type*} {κ : ι → Type*}
    (f : ((i : ι) × κ i) → ℕ) (hf : Function.Injective f) :
    HasLaw (fun ω : ℕ → ℝ => fun i j => ω (f ⟨i, j⟩))
      (Measure.infinitePi (fun i => Measure.infinitePi
        (fun _ : κ i => gaussianReal 0 1))) GaussianLaw := by
  have hc : HasLaw (MeasurableEquiv.piCurry (fun i (_ : κ i) => ℝ))
      (Measure.infinitePi (fun i => Measure.infinitePi (fun _ : κ i => gaussianReal 0 1)))
      (Measure.infinitePi (fun _ : (i : ι) × κ i => gaussianReal 0 1)) := by
    exact ⟨(MeasurableEquiv.piCurry _).measurable.aemeasurable,
      Measure.infinitePi_map_piCurry (fun i (_ : κ i) => gaussianReal 0 1)⟩
  exact hc.comp (stream_selection_hasLaw f hf)

theorem finite_stream_groups_hasLaw {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (f : ((i : ι) × κ i) → ℕ) (hf : Function.Injective f) :
    HasLaw (fun ω : ℕ → ℝ => fun i j => ω (f ⟨i, j⟩))
      (Measure.pi (fun i => Measure.pi (fun _ : κ i => gaussianReal 0 1))) GaussianLaw := by
  simpa only [Measure.infinitePi_eq_pi] using stream_groups_hasLaw f hf

/-- Joint coordinate independence is proved under the original countable law. -/
theorem stream_selection_independent {ι : Type*}
    (f : ι → ℕ) (hf : Function.Injective f) :
    iIndepFun (fun i (ω : ℕ → ℝ) => ω (f i)) GaussianLaw := by
  exact iIndepFun.precomp hf (iIndepFun_infinitePi (X := fun (_ : ℕ) (x : ℝ) => x)
    (fun _ => measurable_id))

/-- Column-major location of an entry of a block beginning at a column offset. -/
def gaussianBlockIndex (n offset : ℕ) {q : ℕ} (p : Fin n × Fin q) : ℕ :=
  (offset + p.2.val) * n + p.1.val

theorem gaussianBlockIndex_injective (n offset q : ℕ) :
    Function.Injective (gaussianBlockIndex n offset (q := q)) := by
  intro p p' he
  have hjval : p.2.val = p'.2.val := by
    by_contra h
    rcases lt_or_gt_of_ne h with h | h
    · have hm := Nat.mul_le_mul_right n (show p.2.val + 1 ≤ p'.2.val by omega)
      dsimp [gaussianBlockIndex] at he
      nlinarith [p.1.isLt, p'.1.isLt]
    · have hm := Nat.mul_le_mul_right n (show p'.2.val + 1 ≤ p.2.val by omega)
      dsimp [gaussianBlockIndex] at he
      nlinarith [p.1.isLt, p'.1.isLt]
  have hj : p.2 = p'.2 := Fin.ext hjval
  have hi : p.1 = p'.1 := by
    apply Fin.ext
    dsimp [gaussianBlockIndex] at he
    rw [hjval] at he
    omega
  exact Prod.ext hi hj

/-- The actual entries of one contiguous stream block. -/
def gaussianBlock (n q offset : ℕ) (ω : ℕ → ℝ) : Matrix (Fin n) (Fin q) ℝ :=
  fun i j => ω (gaussianBlockIndex n offset (i, j))

theorem gaussianBlock_entries_hasLaw (n q offset : ℕ) :
    HasLaw (fun ω : ℕ → ℝ => fun p : Fin n × Fin q => gaussianBlock n q offset ω p.1 p.2)
      (Measure.pi (fun _ : Fin n × Fin q => gaussianReal 0 1)) GaussianLaw :=
  finite_stream_selection_hasLaw _ (gaussianBlockIndex_injective n offset q)

/-- Widths of the three blocks in their precommitted order. -/
def gaussianBlockWidth (s k ell : ℕ) : Fin 3 → ℕ := ![s, k, ell]

/-- Column offsets are exactly those in `makePlan`. -/
def gaussianBlockOffset (s k : ℕ) : Fin 3 → ℕ := ![0, s, s + k]

def gaussianThreeColumn (s k ell : ℕ)
    (p : (b : Fin 3) × Fin (gaussianBlockWidth s k ell b)) : ℕ :=
  gaussianBlockOffset s k p.1 + p.2.val

theorem gaussianThreeColumn_injective (s k ell : ℕ) :
    Function.Injective (gaussianThreeColumn s k ell) := by
  intro ⟨b, j⟩ ⟨b', j'⟩ he
  fin_cases b <;> fin_cases b' <;>
    simp [gaussianThreeColumn, gaussianBlockOffset] at he
  all_goals first
    | (congr 1; apply Fin.ext; omega)
    | (have hj := j.isLt; have hj' := j'.isLt
       simp [gaussianBlockWidth] at hj hj'
       omega)

/-- The dependent type retains every matrix entry and its actual block. -/
def gaussianThreeIndex (n s k ell : ℕ)
    (p : (b : Fin 3) × (Fin n × Fin (gaussianBlockWidth s k ell b))) : ℕ :=
  gaussianThreeColumn s k ell ⟨p.1, p.2.2⟩ * n + p.2.1.val

theorem gaussianThreeIndex_injective (n s k ell : ℕ) :
    Function.Injective (gaussianThreeIndex n s k ell) := by
  intro ⟨b, i, j⟩ ⟨b', i', j'⟩ he
  have hc : gaussianThreeColumn s k ell ⟨b, j⟩ =
      gaussianThreeColumn s k ell ⟨b', j'⟩ := by
    by_contra h
    rcases lt_or_gt_of_ne h with h | h
    · have hm := Nat.mul_le_mul_right n (show
        gaussianThreeColumn s k ell ⟨b, j⟩ + 1 ≤
        gaussianThreeColumn s k ell ⟨b', j'⟩ by omega)
      dsimp [gaussianThreeIndex] at he
      nlinarith [i.isLt, i'.isLt]
    · have hm := Nat.mul_le_mul_right n (show
        gaussianThreeColumn s k ell ⟨b', j'⟩ + 1 ≤
        gaussianThreeColumn s k ell ⟨b, j⟩ by omega)
      dsimp [gaussianThreeIndex] at he
      nlinarith [i.isLt, i'.isLt]
  have hbj := gaussianThreeColumn_injective s k ell hc
  cases hbj
  have hi : i = i' := by
    apply Fin.ext
    dsimp [gaussianThreeIndex] at he
    omega
  cases hi
  rfl

/-- The three actual blocks jointly have their finite product Gaussian law. -/
theorem gaussianThreeBlocks_hasLaw (n s k ell : ℕ) :
    HasLaw (fun ω : ℕ → ℝ => fun b (p : Fin n × Fin (gaussianBlockWidth s k ell b)) =>
      gaussianBlock n (gaussianBlockWidth s k ell b) (gaussianBlockOffset s k b) ω p.1 p.2)
      (Measure.pi (fun b : Fin 3 => Measure.pi
        (fun _ : Fin n × Fin (gaussianBlockWidth s k ell b) => gaussianReal 0 1)))
      GaussianLaw := by
  exact finite_stream_groups_hasLaw _ (gaussianThreeIndex_injective n s k ell)

/-- Joint independence, stronger than pairwise independence, follows from the joint law. -/
theorem gaussianThreeBlocks_independent (n s k ell : ℕ) :
    iIndepFun (fun b (ω : ℕ → ℝ) (p : Fin n × Fin (gaussianBlockWidth s k ell b)) =>
      gaussianBlock n (gaussianBlockWidth s k ell b) (gaussianBlockOffset s k b) ω p.1 p.2)
      GaussianLaw := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (by intro b; exact
    (gaussianBlock_entries_hasLaw n (gaussianBlockWidth s k ell b)
      (gaussianBlockOffset s k b)).aemeasurable)).2
  rw [(gaussianThreeBlocks_hasLaw n s k ell).map_eq]
  congr 1
  funext b
  exact (gaussianBlock_entries_hasLaw n (gaussianBlockWidth s k ell b)
    (gaussianBlockOffset s k b)).map_eq.symm

/-- In the sketch branch these are literally the program's stored Gaussian matrices. -/
theorem makePlan_sketch_blocks (n m : ℕ) (ε : ℝ)
    (hsketch : firstWidth m ε + secondWidth m ε + thirdWidth m ε < n) (ω : ℕ → ℝ) :
    makePlan n m ε ω =
      { full := false, s := firstWidth m ε, k := secondWidth m ε, ell := thirdWidth m ε,
        G0 := gaussianBlock n (firstWidth m ε) 0 ω,
        G1 := gaussianBlock n (secondWidth m ε) (firstWidth m ε) ω,
        H := gaussianBlock n (thirdWidth m ε) (firstWidth m ε + secondWidth m ε) ω } := by
  simp only [makePlan, not_le.mpr hsketch, ↓reduceIte]
  congr 1
  funext i j
  simp [gaussianBlock, gaussianBlockIndex]

#assert_trust kernel stream_coordinate_hasLaw
#assert_trust kernel stream_selection_hasLaw
#assert_trust kernel finite_stream_selection_hasLaw
#assert_trust kernel stream_groups_hasLaw
#assert_trust kernel finite_stream_groups_hasLaw
#assert_trust kernel stream_selection_independent
#assert_trust kernel gaussianBlockIndex_injective
#assert_trust kernel gaussianBlock_entries_hasLaw
#print axioms stream_coordinate_hasLaw
#print axioms stream_selection_hasLaw
#print axioms finite_stream_selection_hasLaw
#print axioms stream_groups_hasLaw
#print axioms finite_stream_groups_hasLaw
#print axioms stream_selection_independent
#print axioms gaussianBlockIndex_injective
#print axioms gaussianBlock_entries_hasLaw
#assert_trust kernel gaussianThreeColumn_injective
#print axioms gaussianThreeColumn_injective
#assert_trust kernel gaussianThreeIndex_injective
#print axioms gaussianThreeIndex_injective
#assert_trust kernel gaussianThreeBlocks_hasLaw
#print axioms gaussianThreeBlocks_hasLaw
#assert_trust kernel gaussianThreeBlocks_independent
#print axioms gaussianThreeBlocks_independent
#assert_trust kernel makePlan_sketch_blocks
#print axioms makePlan_sketch_blocks
end NLA.Proofs.RE06
