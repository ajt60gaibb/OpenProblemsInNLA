import NLA.Proofs.SP11.GardenExpansion

/-!
# Finite recursion trees with shared node labels

A node carries a vertex label, not a fresh polynomial variable. Different
occurrences of that label are evaluated using the same alternating form.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.SP11

/-- A finite rooted tree whose ordered child arity is fixed by its vertex label. -/
inductive GardenTree (V : Type*) (arity : V → ℕ) where
  | node (v : V) (children : Fin (arity v) → GardenTree V arity) : GardenTree V arity

namespace GardenTree

variable {V R : Type*} {arity : V → ℕ} [CommRing R] {d : ℕ}

/-- One output-conduit color at every actual node occurrence. -/
def Coloring (d : ℕ) : GardenTree V arity → Type _
  | .node v children => Fin d × ((s : Fin (arity v)) → Coloring d (children s))

noncomputable instance coloringFintype (d : ℕ) (t : GardenTree V arity) :
    Fintype (Coloring d t) := by
  induction t with
  | node v children ih =>
    change Fintype (Fin d × ((s : Fin (arity v)) → Coloring d (children s)))
    letI : (s : Fin (arity v)) → Fintype (Coloring d (children s)) := ih
    infer_instance

/-- The output color at the root of a tree. -/
def rootColor : {t : GardenTree V arity} → Coloring d t → Fin d
  | .node _ _, c => c.1

/-- Evaluate a tree by the actual shared form associated to each label. -/
noncomputable def value
    (a : (v : V) → (CoordinateVector R d) [⋀^Fin (arity v + 1)]→ₗ[R] R) :
    GardenTree V arity → CoordinateVector R d
  | .node v children => alternatingContraction (a v) (fun s => value a (children s))

/-- The scalar contribution of one complete conduit coloring. The product uses
all occurrences while the label-indexed forms remain shared. -/
noncomputable def weight
    (a : (v : V) → (CoordinateVector R d) [⋀^Fin (arity v + 1)]→ₗ[R] R) :
    (t : GardenTree V arity) → Coloring d t → R
  | .node v children, c =>
      a v (Matrix.vecCons (Pi.single c.1 1)
        (fun s => Pi.single (rootColor (c.2 s)) 1)) *
      ∏ s, weight a (children s) (c.2 s)

/-- Multilinearity yields a finite sum over all conduit colorings. This does not
identify or discard different colorings with the same shared-variable monomial. -/
theorem value_eq_sum_weight
    (a : (v : V) → (CoordinateVector R d) [⋀^Fin (arity v + 1)]→ₗ[R] R)
    (t : GardenTree V arity) :
    value a t = ∑ c : Coloring d t, weight a t c • Pi.single (rootColor c) 1 := by
  classical
  induction t with
  | node v children ih =>
    ext q
    change alternatingContraction (a v) (fun s => value a (children s)) q = _
    have hval : (fun s => value a (children s)) =
        fun s => ∑ c : Coloring d (children s),
          weight a (children s) c • Pi.single (rootColor c) 1 := funext ih
    rw [hval]
    change (a v).curryLeft (Pi.single q 1) _ = _
    have hsum := ((a v).curryLeft (Pi.single q 1)).toMultilinearMap.map_sum
      (fun s c => weight a (children s) c • Pi.single (rootColor c) 1)
    change (a v).curryLeft (Pi.single q 1)
        (fun s => ∑ c : Coloring d (children s),
          weight a (children s) c • Pi.single (rootColor c) 1) =
      ∑ cs : (s : Fin (arity v)) → Coloring d (children s),
        (a v).curryLeft (Pi.single q 1)
          (fun s => weight a (children s) (cs s) • Pi.single (rootColor (cs s)) 1) at hsum
    rw [hsum]
    simp_rw [AlternatingMap.map_smul_univ]
    simp only [smul_eq_mul]
    change (∑ cs : (s : Fin (arity v)) → Coloring d (children s),
      (∏ s, weight a (children s) (cs s)) *
        a v (Matrix.vecCons (Pi.single q 1)
          (fun s => Pi.single (rootColor (cs s)) 1))) = _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change _ = ∑ c : Fin d × ((s : Fin (arity v)) → Coloring d (children s)),
      weight a (.node v children) c *
        (Pi.single c.1 (1 : R) : CoordinateVector R d) q
    rw [Fintype.sum_prod_type]
    simp only [weight, rootColor]
    simp [Pi.single_apply, mul_comm]

end GardenTree

#assert_trust kernel GardenTree.value_eq_sum_weight
#print axioms GardenTree.value_eq_sum_weight

end NLA.Proofs.SP11
