import NLA.Proofs.SP11.GardenExpansion

/-!
# Basis coefficients for every conduit-color tuple

Every injective tuple is sorted by an actual coordinate subset and a finite
permutation. Repeated colors give zero; distinct colors give the signed shared
variable of their sorted subset.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP11

/-- A distinct coordinate tuple is precisely a permutation of a unique
increasing subset. The permutation does not create new coefficient names. -/
theorem exists_sorted_coordinate_tuple {d r : ℕ} (c : Fin r → Fin d)
    (hc : Function.Injective c) :
    ∃ (s : CoordinateSubset d r) (p : Equiv.Perm (Fin r)),
      ∀ i, c i = s.val (p i) := by
  classical
  let S := Finset.univ.image c
  have hcard : S.card = r := by
    simp only [S, Finset.card_image_of_injective _ hc, Finset.card_univ,
      Fintype.card_fin]
  let e : Fin r ≃o S := S.orderIsoOfFin hcard
  let s : CoordinateSubset d r := ⟨S.orderEmbOfFin hcard, (S.orderEmbOfFin hcard).strictMono⟩
  let f : Fin r → Fin r := fun i => e.symm ⟨c i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hf (i : Fin r) : s.val (f i) = c i := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨c i,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
  have hfi : Function.Injective f := by
    intro i j hij
    apply hc
    rw [← hf i, ← hf j, hij]
  let p : Equiv.Perm (Fin r) := Equiv.ofBijective f
    ⟨hfi, Finite.surjective_of_injective hfi⟩
  exact ⟨s, p, fun i => (hf i).symm⟩

/-- No favorable presentation of a color tuple is assumed: injectivity alone
supplies the actual subset, permutation, and signed named coefficient. -/
theorem polynomialAlternatingForm_basis_injective
    {R V : Type*} [CommRing R] {d r : ℕ}
    (name : CoordinateSubset d r → V) (c : Fin r → Fin d)
    (hc : Function.Injective c) :
    ∃ (s : CoordinateSubset d r) (p : Equiv.Perm (Fin r)),
      (∀ i, c i = s.val (p i)) ∧
      polynomialAlternatingForm (R := R) name (fun i => Pi.single (c i) 1) =
        Equiv.Perm.sign p • MvPolynomial.X (name s) := by
  obtain ⟨s, p, hp⟩ := exists_sorted_coordinate_tuple c hc
  refine ⟨s, p, hp, ?_⟩
  simp_rw [hp]
  exact polynomialAlternatingForm_basis_perm name s p

/-- A concrete increasing representative, obtained from the proved finite
sorting theorem. Proof arguments are propositions and do not name variables. -/
noncomputable def sortedColors {d r : ℕ} (c : Fin r → Fin d)
    (hc : Function.Injective c) : CoordinateSubset d r :=
  Classical.choose (exists_sorted_coordinate_tuple c hc)

/-- The finite permutation sorting the actual color tuple. -/
noncomputable def colorPermutation {d r : ℕ} (c : Fin r → Fin d)
    (hc : Function.Injective c) : Equiv.Perm (Fin r) :=
  Classical.choose (Classical.choose_spec (exists_sorted_coordinate_tuple c hc))

theorem sortedColors_spec {d r : ℕ} (c : Fin r → Fin d)
    (hc : Function.Injective c) (i : Fin r) :
    c i = (sortedColors c hc).val (colorPermutation c hc i) :=
  Classical.choose_spec (Classical.choose_spec (exists_sorted_coordinate_tuple c hc)) i

/-- Exponent of one node occurrence. A repeated-color zero term is assigned
zero exponent; its coefficient below is zero. -/
noncomputable def colorExponent {V : Type*} {d r : ℕ}
    (name : CoordinateSubset d r → V) (c : Fin r → Fin d) : V →₀ ℕ := by
  classical
  exact if hc : Function.Injective c then
    Finsupp.single (name (sortedColors c hc)) 1 else 0

/-- Actual signed coefficient of a node, including zero at repeated colors. -/
noncomputable def colorSign (R : Type*) [CommRing R] {d r : ℕ}
    (c : Fin r → Fin d) : R := by
  classical
  exact if hc : Function.Injective c then
    Equiv.Perm.sign (colorPermutation c hc) • (1 : R) else 0

/-- Every basis coefficient is literally one signed monomial or zero. This is
for arbitrary color tuples, with no sorted-presentation hypothesis. -/
theorem polynomialAlternatingForm_basis_eq_monomial
    {R V : Type*} [CommRing R] {d r : ℕ}
    (name : CoordinateSubset d r → V) (c : Fin r → Fin d) :
    polynomialAlternatingForm (R := R) name (fun i => Pi.single (c i) 1) =
      MvPolynomial.monomial (colorExponent name c) (colorSign R c) := by
  classical
  by_cases hc : Function.Injective c
  · have he : (fun i => (Pi.single (c i) (1 : MvPolynomial V R) :
          CoordinateVector (MvPolynomial V R) d)) =
        fun i => Pi.single ((sortedColors c hc).val (colorPermutation c hc i)) 1 := by
      funext i
      rw [sortedColors_spec c hc i]
    rw [he, polynomialAlternatingForm_basis_perm]
    simp only [colorExponent, colorSign, dif_pos hc, MvPolynomial.X,
      MvPolynomial.smul_monomial]
  · rw [polynomialAlternatingForm_basis_eq_zero_of_not_injective name c hc]
    simp only [colorExponent, colorSign, dif_neg hc, map_zero]

/-- Admissible node coefficients are units, hence never vanish in a nontrivial
coefficient ring. No occurrence-independence hypothesis is involved. -/
theorem colorSign_ne_zero {R : Type*} [CommRing R] [Nontrivial R]
    {d r : ℕ} (c : Fin r → Fin d) (hc : Function.Injective c) :
    colorSign R c ≠ 0 := by
  classical
  simp only [colorSign, dif_pos hc]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (colorPermutation c hc)) with hs | hs
  · simp [hs]
  · simp [hs]

#assert_trust kernel exists_sorted_coordinate_tuple
#assert_trust kernel polynomialAlternatingForm_basis_injective
#assert_trust kernel sortedColors_spec
#assert_trust kernel polynomialAlternatingForm_basis_eq_monomial
#assert_trust kernel colorSign_ne_zero
#print axioms exists_sorted_coordinate_tuple
#print axioms polynomialAlternatingForm_basis_eq_monomial

end NLA.Proofs.SP11
