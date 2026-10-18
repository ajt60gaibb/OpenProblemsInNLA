import NLA.Proofs.SP12.GramDifferential
import NLA.Proofs.SP12.ExtendedRows
import NLA.Proofs.SP12.NeighborhoodLifting

/-!
# Actual one-vertex PSD/SAP Gram extension

Local surjectivity of the old nonedge Gram coordinates supplies an old factor
with exactly the small cancelling entries. Openness retains SAP on the fixed
larger graph test space and retains all old edges. One nonzero scalar makes
all new required edges nonzero. No rank-stratum manifold or continuous choice
of factors is assumed.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Topology Matrix.Norms.Elementwise
open Filter Set
open NLA.Proofs.SP11

namespace NLA.Proofs.SP12

/-- The actual new-edge coordinates use one common small nonzero scalar. -/
noncomputable def addedCoordinates {h : ℕ} (G : SimpleGraph (Fin (h + 1)))
    (ε : ℝ) : Fin h → ℝ := by
  classical
  exact fun i => if G.Adj 0 i.succ then ε else 0

@[simp] theorem addedCoordinates_zero {h : ℕ} (G : SimpleGraph (Fin (h + 1))) :
    addedCoordinates G 0 = 0 := by
  classical
  ext i
  simp [addedCoordinates]

theorem continuous_addedCoordinates {h : ℕ} (G : SimpleGraph (Fin (h + 1))) :
    Continuous (addedCoordinates G) := by
  classical
  apply continuous_pi
  intro i
  by_cases hi : G.Adj 0 i.succ
  · convert (continuous_id : Continuous (fun ε : ℝ => ε)) using 1
    funext ε
    simp [addedCoordinates, hi]
  · convert (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))) using 1
    funext ε
    simp [addedCoordinates, hi]

/-- The nonedge target cancels the exact rank-one added-coordinate term. -/
noncomputable def extensionTarget {h : ℕ} (G : SimpleGraph (Fin (h + 1))) (ε : ℝ) :
    (NonedgePair (G.comap Fin.succ) → ℝ) × (Fin h → ℝ) :=
  ((fun p => -(addedCoordinates G ε p.val.1 * addedCoordinates G ε p.val.2)),
    addedCoordinates G ε)

@[simp] theorem extensionTarget_zero {h : ℕ} (G : SimpleGraph (Fin (h + 1))) :
    extensionTarget G 0 = (0, 0) := by
  ext <;> simp [extensionTarget]

theorem continuous_extensionTarget {h : ℕ} (G : SimpleGraph (Fin (h + 1))) :
    Continuous (extensionTarget G) := by
  apply Continuous.prodMk _ (continuous_addedCoordinates G)
  apply continuous_pi
  intro p
  exact (((continuous_apply p.val.1).comp (continuous_addedCoordinates G)).mul
    ((continuous_apply p.val.2).comp (continuous_addedCoordinates G))).neg

private theorem gram_entry_symm {n d : ℕ} (R : Matrix (Fin n) (Fin d) ℝ)
    (i j : Fin n) : gram R i j = gram R j i := by
  simp only [gram_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- Equality of the actual unordered coordinate map controls every old nonedge. -/
theorem gram_nonedge_eq_of_nonedgeGram {h d : ℕ} (H : SimpleGraph (Fin h))
    (R : Matrix (Fin h) (Fin d) ℝ) (b : Fin h → ℝ)
    (hF : nonedgeGram H R = fun p => -(b p.val.1 * b p.val.2))
    (i j : Fin h) (hij : i ≠ j) (hn : ¬ H.Adj i j) :
    gram R i j = -(b i * b j) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact congrFun hF ⟨(i, j), hlt, hn⟩
  · have h := congrFun hF ⟨(j, i), hgt, fun ha => hn ha.symm⟩
    rw [gram_entry_symm R i j]
    simpa only [nonedgeGram, mul_comm] using h

/-- Adding one arbitrary vertex preserves an actual SAP Gram realization while
increasing its ambient dimension by one. This includes empty old graphs. -/
theorem exists_vertexExtension {h d : ℕ} (G : SimpleGraph (Fin (h + 1)))
    (R : Matrix (Fin h) (Fin d) ℝ)
    (hpat : NLA.Statements.SP12.HasPattern (G.comap Fin.succ) (gram R))
    (hsap : NLA.Statements.SP12.StrongArnold (gram R)) :
    ∃ S : Matrix (Fin (h + 1)) (Fin (d + 1)) ℝ,
      NLA.Statements.SP12.HasPattern G (gram S) ∧
      NLA.Statements.SP12.StrongArnold (gram S) := by
  classical
  let U : Set (Matrix (Fin h) (Fin d) ℝ × (Fin h → ℝ)) :=
    {p | Function.Injective (testMultiplication G (gram (extendedRows p.1 p.2))) ∧
      ∀ i j : Fin h, G.Adj i.succ j.succ → gram (extendedRows p.1 p.2) i.succ j.succ ≠ 0}
  have hU : U ∈ 𝓝 (R, (0 : Fin h → ℝ)) := by
    have hs : {A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ |
        Function.Injective (testMultiplication G A)} ∈ 𝓝 (gram (extendedRows R 0)) :=
      (isOpen_injective_testMultiplication G).mem_nhds
        (injective_testMultiplication_extendedRows_zero G R hpat hsap)
    have hs' : ∀ᶠ p : Matrix (Fin h) (Fin d) ℝ × (Fin h → ℝ) in 𝓝 (R, 0),
        Function.Injective (testMultiplication G (gram (extendedRows p.1 p.2))) :=
      (continuous_gram_extendedRows (h := h) (d := d)).continuousAt
        (x := (R, (0 : Fin h → ℝ))) hs
    have he : ∀ᶠ p : Matrix (Fin h) (Fin d) ℝ × (Fin h → ℝ) in 𝓝 (R, 0),
        ∀ i j : Fin h, G.Adj i.succ j.succ → gram (extendedRows p.1 p.2) i.succ j.succ ≠ 0 := by
      apply Filter.eventually_all.mpr
      intro i
      apply Filter.eventually_all.mpr
      intro j
      by_cases hij : G.Adj i.succ j.succ
      · have hn : gram (extendedRows R (0 : Fin h → ℝ)) i.succ j.succ ≠ 0 := by
          simpa only [gram_extendedRows_succ_succ, Pi.zero_apply, zero_mul, zero_add] using
            (hpat.2 i j ((G.comap Fin.succ).ne_of_adj hij)).mpr hij
        have hc : Continuous (fun p : Matrix (Fin h) (Fin d) ℝ × (Fin h → ℝ) =>
            gram (extendedRows p.1 p.2) i.succ j.succ) :=
          (continuous_apply j.succ).comp ((continuous_apply i.succ).comp (continuous_gram_extendedRows (h := h) (d := d)))
        exact (hc.continuousAt.eventually_ne hn).mono (fun _ hp _ => hp)
      · exact Filter.Eventually.of_forall (fun _ ha => (hij ha).elim)
    exact hs'.and he
  have ht : Tendsto (extensionTarget G) (𝓝 0) (𝓝 (0, 0)) := by
    have ht0 := (continuous_extensionTarget G).continuousAt (x := 0)
    change Tendsto (extensionTarget G) (𝓝 0) (𝓝 (extensionTarget G 0)) at ht0
    rwa [extensionTarget_zero] at ht0
  obtain ⟨ε, hε, p, hp, hpair⟩ := exists_nonzero_lift_in_nhds
    (nonedgeGram (G.comap Fin.succ)) R (map_nonedgeGram_nhds (G.comap Fin.succ) R hpat hsap)
    U hU (extensionTarget G) ht
  rcases p with ⟨R', b⟩
  have hF : nonedgeGram (G.comap Fin.succ) R' =
      fun p => -(addedCoordinates G ε p.val.1 * addedCoordinates G ε p.val.2) :=
    congrArg Prod.fst hpair
  have hb : b = addedCoordinates G ε := congrArg Prod.snd hpair
  subst b
  let S := extendedRows R' (addedCoordinates G ε)
  have hp' : Function.Injective (testMultiplication G (gram S)) ∧
      ∀ i j : Fin h, G.Adj i.succ j.succ → gram S i.succ j.succ ≠ 0 := hp
  have hnew (i : Fin h) : addedCoordinates G ε i ≠ 0 ↔ G.Adj 0 i.succ := by
    by_cases hi : G.Adj 0 i.succ <;> simp [addedCoordinates, hi, hε]
  have hpattern : NLA.Statements.SP12.HasPattern G (gram S) := by
    apply gram_hasPattern G S
    intro i j hij
    change gram S i j ≠ 0 ↔ G.Adj i j
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => simpa only [S, gram_extendedRows_zero_succ] using hnew j
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        simpa only [S, gram_extendedRows_succ_zero] using (hnew i).trans (G.adj_comm 0 i.succ)
      | succ j =>
        by_cases hadj : G.Adj i.succ j.succ
        · exact iff_of_true (hp'.2 i j hadj) hadj
        · have hzero : gram S i.succ j.succ = 0 := by
            change gram (extendedRows R' (addedCoordinates G ε)) i.succ j.succ = 0
            rw [gram_extendedRows_succ_succ,
              gram_nonedge_eq_of_nonedgeGram (G.comap Fin.succ) R' (addedCoordinates G ε)
                hF i j (fun he => hij (congrArg Fin.succ he)) hadj]
            ring
          simp only [hzero, ne_eq, not_true_eq_false, hadj]
  exact ⟨S, hpattern,
    (strongArnold_iff_injective_testMultiplication G (gram S) hpattern).mpr hp'.1⟩

#assert_trust kernel exists_vertexExtension
#print axioms exists_vertexExtension

end NLA.Proofs.SP12
