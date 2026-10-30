import NLA.Proofs.TR04.ReshapeFrobenius
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn

/-! Auxiliary tensor formats with no dimension or order lower bounds.  The
original Shape and its target are unchanged.  Explicit finite index bijections
make these formats suitable for recursive tensor-train compression. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators

namespace NLA.Proofs.TR04.TensorFormat

/-- A recursive finite product, including the empty product and empty factors. -/
abbrev Index : List ℕ → Type
  | [] => PUnit
  | m :: ns => Fin m × Index ns

instance indexFintype : (ns : List ℕ) → Fintype (Index ns)
  | [] => inferInstanceAs (Fintype PUnit)
  | m :: ns =>
    letI := indexFintype ns
    inferInstanceAs (Fintype (Fin m × Index ns))

abbrev Tensor (ns : List ℕ) := Index ns → ℝ

/-- Split at a cut after exactly k modes; beyond the last mode the suffix is empty. -/
def splitIndex : (ns : List ℕ) → (k : ℕ) →
    Index ns → Index (ns.take k) × Index (ns.drop k)
  | [], 0 => fun _ => (PUnit.unit, PUnit.unit)
  | [], _ + 1 => fun _ => (PUnit.unit, PUnit.unit)
  | _ :: _, 0 => fun x => (PUnit.unit, x)
  | _ :: ns, k + 1 => fun x =>
    ((x.1, (splitIndex ns k x.2).1), (splitIndex ns k x.2).2)

def joinIndex : (ns : List ℕ) → (k : ℕ) →
    Index (ns.take k) → Index (ns.drop k) → Index ns
  | [], _ => fun _ _ => PUnit.unit
  | _ :: _, 0 => fun _ x => x
  | _ :: ns, k + 1 => fun x y => (x.1, joinIndex ns k x.2 y)

@[simp] theorem joinIndex_zero (ns : List ℕ) (x : Index (ns.take 0)) (y : Index ns) :
    joinIndex ns 0 x y = y := by
  cases ns with
  | nil => cases y; rfl
  | cons m ns => rfl

@[simp] theorem join_splitIndex (ns : List ℕ) (k : ℕ) (x : Index ns) :
    joinIndex ns k (splitIndex ns k x).1 (splitIndex ns k x).2 = x := by
  induction ns generalizing k with
  | nil => cases x; rfl
  | cons m ns ih =>
    cases k with
    | zero => rfl
    | succ k =>
      change (x.1, joinIndex ns k (splitIndex ns k x.2).1 (splitIndex ns k x.2).2) = x
      rw [ih]

@[simp] theorem split_joinIndex (ns : List ℕ) (k : ℕ)
    (x : Index (ns.take k)) (y : Index (ns.drop k)) :
    splitIndex ns k (joinIndex ns k x y) = (x, y) := by
  induction ns generalizing k with
  | nil => cases k <;> cases x <;> cases y <;> rfl
  | cons m ns ih =>
    cases k with
    | zero => cases x; rfl
    | succ k =>
      change Fin m × Index (ns.take k) at x
      change Index (ns.drop k) at y
      rcases x with ⟨a, x⟩
      change ((a, (splitIndex ns k (joinIndex ns k x y)).1),
        (splitIndex ns k (joinIndex ns k x y)).2) = ((a, x), y)
      rw [ih]

def splitEquiv (ns : List ℕ) (k : ℕ) :
    Index ns ≃ Index (ns.take k) × Index (ns.drop k) where
  toFun := splitIndex ns k
  invFun xy := joinIndex ns k xy.1 xy.2
  left_inv := join_splitIndex ns k
  right_inv xy := split_joinIndex ns k xy.1 xy.2

/-- The actual entries, without truncating or dropping any tensor coordinate. -/
def unfold (ns : List ℕ) (A : Tensor ns) (k : ℕ) :
    Matrix (Index (ns.take k)) (Index (ns.drop k)) ℝ :=
  fun x y => A (joinIndex ns k x y)

def unfoldLinearEquiv (ns : List ℕ) (k : ℕ) :
    Tensor ns ≃ₗ[ℝ] Matrix (Index (ns.take k)) (Index (ns.drop k)) ℝ where
  toFun A := unfold ns A k
  invFun M x := M (splitIndex ns k x).1 (splitIndex ns k x).2
  left_inv A := by funext x; simp [unfold]
  right_inv M := by funext x y; simp [unfold]
  map_add' A B := rfl
  map_smul' c A := rfl

def energy (ns : List ℕ) (A : Tensor ns) : ℝ := ∑ x, (A x)^2

def error (ns : List ℕ) (A B : Tensor ns) : ℝ := energy ns (A - B)

theorem energy_nonneg (ns : List ℕ) (A : Tensor ns) : 0 ≤ energy ns A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem energy_unfold (ns : List ℕ) (A : Tensor ns) (k : ℕ) :
    energy ns A = ∑ x, ∑ y, (unfold ns A k x y)^2 := by
  have h := (splitEquiv ns k).symm.sum_comp (fun x => (A x)^2)
  change (∑ p : Index (ns.take k) × Index (ns.drop k),
    (A (joinIndex ns k p.1 p.2))^2) = energy ns A at h
  simpa only [Fintype.sum_prod_type, unfold] using h.symm

@[simp] theorem unfold_zero (ns : List ℕ) (k : ℕ) : unfold ns 0 k = 0 := rfl
@[simp] theorem unfold_sub (ns : List ℕ) (A B : Tensor ns) (k : ℕ) :
    unfold ns (A - B) k = unfold ns A k - unfold ns B k := rfl

theorem error_unfold (ns : List ℕ) (A B : Tensor ns) (k : ℕ) :
    error ns A B = ∑ x, ∑ y, (unfold ns A k x y - unfold ns B k x y)^2 :=
  energy_unfold ns (A - B) k

@[simp] theorem energy_zero (ns : List ℕ) : energy ns 0 = 0 := by simp [energy]
@[simp] theorem error_zero_right (ns : List ℕ) (A : Tensor ns) : error ns A 0 = energy ns A := by
  simp [error]

theorem error_nonneg (ns : List ℕ) (A B : Tensor ns) : 0 ≤ error ns A B :=
  energy_nonneg ns (A - B)

theorem card_index (ns : List ℕ) : Fintype.card (Index ns) = ns.prod := by
  induction ns with
  | nil => simp [Index]
  | cons m ns ih =>
    simpa only [Index, Fintype.card_prod, Fintype.card_fin, List.prod_cons] using congrArg (fun k => m * k) ih

/-- The actual finite mode vector as a recursive list. -/
abbrev modeList : {d : ℕ} → (Fin d → ℕ) → List ℕ
  | 0, _ => []
  | d + 1, n => n 0 :: modeList (fun i : Fin d => n i.succ)

theorem modeList_eq_ofFn {d : ℕ} (n : Fin d → ℕ) : modeList n = List.ofFn n := by
  induction d with
  | zero => simp [modeList]
  | succ d ih => simp only [modeList, List.ofFn_succ, ih]

theorem length_modeList {d : ℕ} (n : Fin d → ℕ) : (modeList n).length = d := by
  rw [modeList_eq_ofFn]
  simp

/-- The recursion-compatible actual tensor index equivalence. -/
def vectorIndexEquiv : {d : ℕ} → (n : Fin d → ℕ) →
    Index (modeList n) ≃ ((i : Fin d) → Fin (n i))
  | 0, _ =>
    { toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => PUnit.unit
      left_inv := fun _x => Subsingleton.elim _ _
      right_inv := fun _x => funext (fun i => Fin.elim0 i) }
  | d + 1, n =>
      (Equiv.prodCongr (Equiv.refl (Fin (n 0))) (vectorIndexEquiv (fun i : Fin d => n i.succ))).trans
        (Fin.consEquiv (fun i => Fin (n i)))

/-- Index equivalence for a mode vector: no size/order restrictions occur here. -/
def ofFnIndexEquiv : {d : ℕ} → (n : Fin d → ℕ) →
    Index (List.ofFn n) ≃ ((i : Fin d) → Fin (n i))
  | 0, n => by
    simpa only [List.ofFn_zero, Index] using (Equiv.equivPUnit ((i : Fin 0) → Fin (n i))).symm
  | d + 1, n => by
    simpa only [List.ofFn_succ, Index] using
      (Equiv.prodCongr (Equiv.refl (Fin (n 0))) (ofFnIndexEquiv (fun i : Fin d => n i.succ))).trans
        (Fin.consEquiv (fun i => Fin (n i)))

/-- Literal original tensor entries reindexed by the proved finite-product bijection. -/
def originalTensorLinearEquiv (S : NLA.Computation.TensorTrainApproximation.Shape) :
    NLA.Computation.TensorTrainApproximation.Tensor S ≃ₗ[ℝ]
      Tensor (modeList S.mode) where
  toFun A x := A (vectorIndexEquiv S.mode x)
  invFun A x := A ((vectorIndexEquiv S.mode).symm x)
  left_inv A := by funext x; simp
  right_inv A := by funext x; simp
  map_add' A B := rfl
  map_smul' c A := rfl

theorem original_error_eq (S : NLA.Computation.TensorTrainApproximation.Shape)
    (A B : NLA.Computation.TensorTrainApproximation.Tensor S) :
    NLA.Computation.TensorTrainApproximation.FrobeniusSq S A B =
      error (modeList S.mode) (originalTensorLinearEquiv S A)
        (originalTensorLinearEquiv S B) := by
  exact ((vectorIndexEquiv S.mode).sum_comp (fun x => (A x - B x)^2)).symm

#assert_trust kernel splitEquiv
#assert_trust kernel unfoldLinearEquiv
#assert_trust kernel energy_unfold
#assert_trust kernel error_unfold
#assert_trust kernel modeList_eq_ofFn
#assert_trust kernel vectorIndexEquiv
#assert_trust kernel ofFnIndexEquiv
#assert_trust kernel originalTensorLinearEquiv
#assert_trust kernel original_error_eq
#print axioms original_error_eq
end NLA.Proofs.TR04.TensorFormat
