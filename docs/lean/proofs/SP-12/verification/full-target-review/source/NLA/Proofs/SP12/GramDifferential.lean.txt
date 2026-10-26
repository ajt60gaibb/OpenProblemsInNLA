import NLA.Proofs.SP11.GramBridge
import NLA.Proofs.SP12.SAPTestSpace
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Matrix.Basis

/-! The actual unordered-nonedge coordinates of the Gram map and its differential.
No matrix rank manifold or assumed local surjectivity is used. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Matrix.Norms.Elementwise

namespace NLA.Proofs.SP12

abbrev NonedgePair {n : ℕ} (G : SimpleGraph (Fin n)) :=
  {ij : Fin n × Fin n // ij.1 < ij.2 ∧ ¬ G.Adj ij.1 ij.2}

noncomputable instance nonedgePairFintype {n : ℕ} (G : SimpleGraph (Fin n)) :
    Fintype (NonedgePair G) := Fintype.ofFinite _

def nonedgeGram {n d : ℕ} (G : SimpleGraph (Fin n))
    (R : Matrix (Fin n) (Fin d) ℝ) : NonedgePair G → ℝ :=
  fun p => NLA.Proofs.SP11.gram R p.val.1 p.val.2

abbrev offGram {n d : ℕ} (G : SimpleGraph (Fin n)) := @nonedgeGram n d G

noncomputable def gramDifferential {n d : ℕ} (G : SimpleGraph (Fin n))
    (R : Matrix (Fin n) (Fin d) ℝ) :
    Matrix (Fin n) (Fin d) ℝ →L[ℝ] (NonedgePair G → ℝ) :=
  ({ toFun := fun D p => ∑ k, (D p.val.1 k * R p.val.2 k + R p.val.1 k * D p.val.2 k)
     map_add' := by
       intro A B
       ext p
       simp [add_mul, mul_add, Finset.sum_add_distrib]
       ring_nf
     map_smul' := by
       intro r D
       ext p
       simp [Finset.mul_sum, mul_add, mul_assoc]
       ring_nf } : Matrix (Fin n) (Fin d) ℝ →ₗ[ℝ] (NonedgePair G → ℝ)).toContinuousLinearMap

@[simp] theorem gramDifferential_apply {n d : ℕ} (G : SimpleGraph (Fin n))
    (R D : Matrix (Fin n) (Fin d) ℝ) (p : NonedgePair G) :
    gramDifferential G R D p =
      ∑ k, (D p.val.1 k * R p.val.2 k + R p.val.1 k * D p.val.2 k) := rfl

theorem gramDifferential_matrix {n d : ℕ} (G : SimpleGraph (Fin n))
    (R D : Matrix (Fin n) (Fin d) ℝ) (p : NonedgePair G) :
    gramDifferential G R D p =
      (D * R.transpose + R * D.transpose) p.val.1 p.val.2 := by
  simp [gramDifferential_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_add_distrib]

/-- The two symmetric placements of one unordered pair, in coordinate space. -/
noncomputable def nonedgeBasis {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    NonedgePair G → ℝ := by
  classical
  exact fun p => (if p.val.1 = i ∧ p.val.2 = j then 1 else 0) +
    (if p.val.2 = i ∧ p.val.1 = j then 1 else 0)

theorem nonedgeBasis_symm {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    nonedgeBasis G i j = nonedgeBasis G j i := by
  classical
  ext p
  simp only [nonedgeBasis, and_comm]
  ring_nf

theorem nonedgeBasis_diag {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) :
    nonedgeBasis G i i = 0 := by
  classical
  ext p
  have hn : p.val.1 ≠ p.val.2 := ne_of_lt p.property.1
  have h1 : ¬ (p.val.1 = i ∧ p.val.2 = i) := by
    rintro ⟨h1, h2⟩
    exact hn (h1.trans h2.symm)
  have h2 : ¬ (p.val.2 = i ∧ p.val.1 = i) := by
    rintro ⟨h2, h1⟩
    exact hn (h1.trans h2.symm)
  simp [nonedgeBasis, h1, h2]

theorem nonedgeBasis_edge {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n)
    (hij : G.Adj i j) : nonedgeBasis G i j = 0 := by
  classical
  ext p
  have hn := p.property.2
  simp only [nonedgeBasis, Pi.zero_apply]
  split_ifs with h1 h2 h2
  all_goals first | exact (hn (by simpa [h1.1, h1.2] using hij)).elim |
    exact (hn (by simpa [h2.1, h2.2] using hij.symm)).elim | norm_num

theorem gramDifferential_single {n d : ℕ} (G : SimpleGraph (Fin n))
    (R : Matrix (Fin n) (Fin d) ℝ) (i : Fin n) (k : Fin d) :
    gramDifferential G R (Matrix.single i k 1) =
      ∑ j : Fin n, R j k • nonedgeBasis G i j := by
  classical
  ext p
  by_cases h1 : p.val.1 = i <;> by_cases h2 : p.val.2 = i
  all_goals simp [gramDifferential_apply, Matrix.single_apply, nonedgeBasis,
    h1, h2, eq_comm, Finset.sum_add_distrib, mul_add, ite_and]
  all_goals simp_all [eq_comm]

noncomputable def matrixEntryCLM {n d : ℕ} (i : Fin n) (k : Fin d) :
    Matrix (Fin n) (Fin d) ℝ →L[ℝ] ℝ :=
  ({ toFun := fun R => R i k
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Matrix (Fin n) (Fin d) ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap

@[simp] theorem matrixEntryCLM_apply {n d : ℕ} (i : Fin n) (k : Fin d)
    (D : Matrix (Fin n) (Fin d) ℝ) : matrixEntryCLM i k D = D i k := rfl

theorem hasStrictFDerivAt_nonedgeGram {n d : ℕ} (G : SimpleGraph (Fin n))
    (R : Matrix (Fin n) (Fin d) ℝ) :
    HasStrictFDerivAt (nonedgeGram G) (gramDifferential G R) R := by
  apply (hasStrictFDerivAt_pi' (𝕜 := ℝ) (Φ := nonedgeGram G)
    (Φ' := gramDifferential G R) (x := R)).mpr
  intro p
  have hk (k : Fin d) := ((matrixEntryCLM p.val.1 k).hasStrictFDerivAt (x := R)).mul
    ((matrixEntryCLM p.val.2 k).hasStrictFDerivAt (x := R))
  have hh := HasStrictFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin d))) (fun k _ => hk k)
  convert hh using 1
  · rfl
  · ext D
    change (∑ k, (D p.val.1 k * R p.val.2 k + R p.val.1 k * D p.val.2 k)) = _
    simp only [sum_apply, add_apply, matrixEntryCLM_apply]
    apply Finset.sum_congr rfl
    intro k _
    change D p.val.1 k * R p.val.2 k + R p.val.1 k * D p.val.2 k =
      R p.val.1 k * D p.val.2 k + R p.val.2 k * D p.val.1 k
    ring_nf

theorem nonedgeBasis_pair {n : ℕ} (G : SimpleGraph (Fin n)) (p : NonedgePair G) :
    nonedgeBasis G p.val.1 p.val.2 = Pi.single p 1 := by
  classical
  ext q
  by_cases hq : q = p
  · subst q
    have hn := ne_of_lt p.property.1
    simp [nonedgeBasis, hn, hn.symm]
  · have h1 : ¬ (q.val.1 = p.val.1 ∧ q.val.2 = p.val.2) := by
      intro he
      apply hq
      exact Subtype.ext (Prod.ext he.1 he.2)
    have h2 : ¬ (q.val.2 = p.val.1 ∧ q.val.1 = p.val.2) := by
      intro he
      have hp := p.property.1
      have hq := q.property.1
      omega
    simp [nonedgeBasis, h1, h2, hq]

/-- No nonzero functional annihilates the actual Gram derivative: its symmetric
nonedge matrix would be a forbidden SAP test matrix. -/
theorem gramDifferential_annihilator_zero {n d : ℕ} (G : SimpleGraph (Fin n))
    (R : Matrix (Fin n) (Fin d) ℝ)
    (hp : NLA.Statements.SP12.HasPattern G (NLA.Proofs.SP11.gram R))
    (hs : NLA.Statements.SP12.StrongArnold (NLA.Proofs.SP11.gram R))
    (φ : (NonedgePair G → ℝ) →ₗ[ℝ] ℝ)
    (hφ : ∀ D, φ (gramDifferential G R D) = 0) : φ = 0 := by
  classical
  let X : Matrix (Fin n) (Fin n) ℝ := fun i j => φ (nonedgeBasis G i j)
  have hsym : ∀ i j, X i j = X j i := by
    intro i j
    exact congrArg φ (nonedgeBasis_symm G i j)
  have hdiag : ∀ i, X i i = 0 := by
    intro i
    dsimp [X]
    rw [nonedgeBasis_diag, map_zero]
  have hedge : ∀ i j, G.Adj i j → X i j = 0 := by
    intro i j hij
    dsimp [X]
    rw [nonedgeBasis_edge G i j hij, map_zero]
  have hXR : X * R = 0 := by
    ext i k
    change (∑ j, X i j * R j k) = 0
    have hh := hφ (Matrix.single i k 1)
    rw [gramDifferential_single, map_sum] at hh
    simpa only [Matrix.mul_apply, Matrix.zero_apply, map_smul, smul_eq_mul,
      X, mul_comm] using hh
  have hXt : X.transpose = X := by
    ext i j
    exact hsym j i
  have hRX : R.transpose * X = 0 := by
    have hh := congrArg Matrix.transpose hXR
    simpa only [Matrix.transpose_mul, hXt, Matrix.transpose_zero] using hh
  have hAX : NLA.Proofs.SP11.gram R * X = 0 := by
    rw [NLA.Proofs.SP11.gram, Matrix.mul_assoc, hRX, Matrix.mul_zero]
  have hhad : ∀ i j, NLA.Proofs.SP11.gram R i j * X i j = 0 := by
    intro i j
    by_cases he : i = j
    · subst j
      rw [hdiag, mul_zero]
    · by_cases ha : G.Adj i j
      · rw [hedge i j ha, mul_zero]
      · have hz : NLA.Proofs.SP11.gram R i j = 0 :=
          not_ne_iff.mp (fun hn => ha ((hp.2 i j he).mp hn))
        rw [hz, zero_mul]
  have hX := hs X hsym hAX hhad hdiag
  have hsingle (p : NonedgePair G) : φ (Pi.single p 1) = 0 := by
    have hh := congrFun (congrFun hX p.val.1) p.val.2
    change φ (nonedgeBasis G p.val.1 p.val.2) = 0 at hh
    rwa [nonedgeBasis_pair] at hh
  apply LinearMap.ext
  intro z
  change φ z = 0
  have hz : z = ∑ p : NonedgePair G, z p • Pi.single p (1 : ℝ) := by
    ext q
    simp [Pi.single_apply]
  rw [hz, map_sum]
  simp [map_smul, hsingle]

theorem gramDifferential_surjective {n d : ℕ} (G : SimpleGraph (Fin n))
    (R : Matrix (Fin n) (Fin d) ℝ)
    (hp : NLA.Statements.SP12.HasPattern G (NLA.Proofs.SP11.gram R))
    (hs : NLA.Statements.SP12.StrongArnold (NLA.Proofs.SP11.gram R)) :
    Function.Surjective (gramDifferential G R) := by
  apply (LinearMap.dualMap_injective_iff (f := (gramDifferential G R).toLinearMap)).mp
  intro φ ψ he
  apply sub_eq_zero.mp
  apply gramDifferential_annihilator_zero G R hp hs (φ - ψ)
  intro D
  have hh := congrArg (fun f : Matrix (Fin n) (Fin d) ℝ →ₗ[ℝ] ℝ => f D) he
  change φ (gramDifferential G R D) = ψ (gramDifferential G R D) at hh
  exact sub_eq_zero.mpr hh

theorem map_nonedgeGram_nhds {n d : ℕ} (G : SimpleGraph (Fin n))
    (R : Matrix (Fin n) (Fin d) ℝ)
    (hp : NLA.Statements.SP12.HasPattern G (NLA.Proofs.SP11.gram R))
    (hs : NLA.Statements.SP12.StrongArnold (NLA.Proofs.SP11.gram R)) :
    Filter.map (nonedgeGram G) (nhds R) = nhds 0 := by
  have hz : nonedgeGram G R = 0 := by
    ext p
    apply not_ne_iff.mp
    intro hn
    exact p.property.2 ((hp.2 _ _ (ne_of_lt p.property.1)).mp hn)
  have hrange : (gramDifferential G R).range = ⊤ :=
    LinearMap.range_eq_top.mpr (gramDifferential_surjective G R hp hs)
  have hh := (hasStrictFDerivAt_nonedgeGram G R).map_nhds_eq_of_surj hrange
  rw [hz] at hh
  convert hh using 1
  rfl

#assert_trust kernel hasStrictFDerivAt_nonedgeGram
#assert_trust kernel gramDifferential_surjective
#assert_trust kernel map_nonedgeGram_nhds
#print axioms map_nonedgeGram_nhds

end NLA.Proofs.SP12
