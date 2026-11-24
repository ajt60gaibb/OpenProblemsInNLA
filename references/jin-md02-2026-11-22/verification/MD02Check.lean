import LovaszTheta.CirculantLimit

open Filter Matrix
open scoped Topology

namespace MD02Verification

open LovaszTheta

/-- A true bit selects its entire inversion class. -/
def sampleGraph {n : ℕ} (x : Circulant.InversionClass n → Bool) : SimpleGraph (ZMod n) :=
  Circulant.graph (reverseSigns (Circulant.InversionClass n) x)

theorem adj_iff_selected {n : ℕ} (x : Circulant.InversionClass n → Bool) (i j : ZMod n) :
    (sampleGraph x).Adj i j ↔ ∃ h : i - j ≠ 0, x (Circulant.inversionClass (i - j) h) = true := by
  change (Circulant.graph (reverseSigns _ x)).Adj i j ↔ _
  rw [Circulant.graph_adj_iff_epsilon]
  by_cases h : i - j = 0
  · norm_num [Circulant.epsilon, h]
  · cases hx : x (Circulant.inversionClass (i - j) h) <;>
      norm_num [Circulant.epsilon, h, hx, sign]

/-- A nonzero self-inverse residue is represented by one class with one residue. -/
theorem inversionClass_singleton {n : ℕ} {s : ZMod n} (hs : s ≠ 0) (h : -s = s) :
    (Circulant.inversionClass s hs).val = {s} := by
  simp [Circulant.inversionClass, h]

/-- Objective values of the real symmetric trace-one SDP in MD-02. -/
def catalogValues {n : ℕ} [NeZero n] (G : SimpleGraph (ZMod n)) : Set ℝ :=
  {v | ∃ X : Matrix (ZMod n) (ZMod n) ℝ,
    X = Xᵀ ∧ X.PosSemidef ∧ X.trace = 1 ∧
      (∀ i j, G.Adj i j → X i j = 0) ∧ (∑ i, ∑ j, X i j) = v}

/-- The formalized theta value is the attained maximum of the catalog SDP. -/
theorem theta_isGreatest {n : ℕ} [NeZero n] (G : SimpleGraph (ZMod n)) :
    IsGreatest (catalogValues G) (theta G) := by
  obtain ⟨X, hX, hMax⟩ := exists_theta_maximizer G
  have hSymm : X = Xᵀ := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hX.1.isHermitian.eq.symm
  refine ⟨⟨X, hSymm, hX.1, hX.2.1, hX.2.2, hMax⟩, ?_⟩
  rintro _ ⟨Y, _, hPSD, hTrace, hEdges, rfl⟩
  exact objective_le_theta ⟨hPSD, hTrace, hEdges⟩

/-- The expectation under one independent fair bit per inversion class. -/
noncomputable def catalogExpectation (n : ℕ) [NeZero n] : ℝ := by
  classical
  exact (∑ x : Circulant.InversionClass n → Bool, sSup (catalogValues (sampleGraph x))) /
    (2 : ℝ) ^ Fintype.card (Circulant.InversionClass n)

theorem catalogExpectation_eq (n : ℕ) [NeZero n] :
    catalogExpectation n = Circulant.expectedTheta n := by
  classical
  unfold catalogExpectation Circulant.expectedTheta
  simp_rw [(theta_isGreatest _).csSup_eq]
  calc
    _ = average (fun x : Circulant.InversionClass n → Bool ↦ theta (sampleGraph x)) := by
      simp [average]
    _ = _ := average_equiv (reverseSigns (Circulant.InversionClass n))
      (fun x ↦ theta (Circulant.graph x))

/-- The MD-02 expectation limit through every order n ≥ 2, indexed by n = m + 2. -/
theorem tendsto_catalogExpectation_div_sqrt :
    Tendsto (fun m : ℕ ↦ catalogExpectation (m + 2) / Real.sqrt (m + 2 : ℕ)) atTop (𝓝 1) := by
  have h := Circulant.tendsto_normalizedExpectedTheta.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun m : ℕ ↦
    Circulant.expectedTheta (m + 1 + 1) / Real.sqrt (m + 1 + 1 : ℕ)) atTop (𝓝 1) at h
  simpa only [catalogExpectation_eq, Nat.add_assoc] using h

end MD02Verification

open Lean Elab Command

run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let targets := #[`MD02Verification.adj_iff_selected, `MD02Verification.inversionClass_singleton,
    `MD02Verification.theta_isGreatest, `MD02Verification.catalogExpectation_eq,
    `MD02Verification.tendsto_catalogExpectation_div_sqrt,
    `LovaszTheta.Circulant.tendsto_normalizedExpectedTheta]
  for target in targets do
    for axiomName in ← collectAxioms target do
      unless allowed.contains axiomName do
        throwError "{target} depends on an unexpected axiom {axiomName}"
  logInfo m!"Checked the transitive axioms of {targets.size} declarations."

#print axioms MD02Verification.adj_iff_selected
#print axioms MD02Verification.inversionClass_singleton
#print axioms MD02Verification.theta_isGreatest
#print axioms MD02Verification.catalogExpectation_eq
#print axioms MD02Verification.tendsto_catalogExpectation_div_sqrt
#print axioms LovaszTheta.Circulant.tendsto_normalizedExpectedTheta
