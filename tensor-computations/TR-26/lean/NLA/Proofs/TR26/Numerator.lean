import NLA.Proofs.TR26.BinaryDefinitions

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR26
open NLA.Statements.TR26
open Polynomial

theorem coordinateEntry_single_diagonal {d : ℕ} (p i j : Index d) (c : ℂ) :
    coordinateEntry (Pi.single (⟨(p,p), le_rfl⟩ : SymIndex d) c) i j =
      if i=p ∧ j=p then c else 0 := by
  classical
  unfold coordinateEntry
  split_ifs <;> simp_all [Pi.single_apply, Subtype.mk.injEq, Prod.mk.injEq, and_comm]

theorem coordinateEntry_single_offdiagonal {d : ℕ} (p q i j : Index d)
    (hpq : p < q) (c : ℂ) :
    coordinateEntry (Pi.single (⟨(p,q), hpq.le⟩ : SymIndex d) c) i j =
      (if i=p ∧ j=q then c else 0) + (if i=q ∧ j=p then c else 0) := by
  classical
  by_cases hij : i ≤ j
  · simp only [coordinateEntry, dif_pos hij, Pi.single_apply,
      Subtype.mk.injEq, Prod.mk.injEq]
    by_cases h1 : i=p ∧ j=q
    · obtain ⟨rfl,rfl⟩ := h1
      simp [hpq.ne, hpq.ne']
    · have h2 : ¬ (i=q ∧ j=p) := by
        rintro ⟨rfl,rfl⟩
        exact (not_le_of_gt hpq) hij
      simp [h1,h2]
  · simp only [coordinateEntry, dif_neg hij, Pi.single_apply,
      Subtype.mk.injEq, Prod.mk.injEq]
    have h1 : ¬ (i=p ∧ j=q) := by
      rintro ⟨rfl,rfl⟩
      exact hij hpq.le
    by_cases h2 : i=q ∧ j=p
    · obtain ⟨rfl,rfl⟩ := h2
      simp [hpq.ne, hpq.ne']
    · have h2' : ¬ (j=p ∧ i=q) := by simpa only [and_comm] using h2
      simp [h1,h2,h2']

theorem affineNumerator_single_diagonal {d : ℕ} (p : Index d) (c : ℂ) :
    affineNumerator (Pi.single (⟨(p,p), le_rfl⟩ : SymIndex d) c) = C c * X^(2*p.val) := by
  classical
  simp only [affineNumeratorOver, coordinateEntry_single_diagonal]
  simp [ite_and, apply_ite C, add_comm, two_mul]

theorem affineNumerator_single_offdiagonal {d : ℕ} (p q : Index d)
    (hpq : p < q) (c : ℂ) :
    affineNumerator (Pi.single (⟨(p,q), hpq.le⟩ : SymIndex d) c) =
      2*C c*X^(p.val+q.val) := by
  classical
  simp only [affineNumeratorOver, coordinateEntry_single_offdiagonal p q _ _ hpq,
    map_add, add_mul, Finset.sum_add_distrib]
  simp [ite_and, apply_ite C, add_comm, two_mul]
  ring

def affineNumeratorLinear (d : ℕ) : Parameter d →ₗ[ℂ] Polynomial ℂ where
  toFun := affineNumerator
  map_add' H K := by
    change affineNumeratorOver (H+K) = affineNumeratorOver H + affineNumeratorOver K
    unfold affineNumeratorOver
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hentry : coordinateEntry (H+K) i j = coordinateEntry H i j+coordinateEntry K i j := by
      unfold coordinateEntry
      split_ifs <;> rfl
    rw [hentry, map_add, add_mul]
  map_smul' c H := by
    change affineNumeratorOver (c • H) = c • affineNumeratorOver H
    unfold affineNumeratorOver
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hentry : coordinateEntry (c • H) i j = c*coordinateEntry H i j := by
      unfold coordinateEntry
      split_ifs <;> rfl
    rw [hentry, map_mul, Polynomial.smul_eq_C_mul]
    ring

def numeratorBasisLeft (d : ℕ) (k : Fin (2*d+1)) : Index d :=
  ⟨k.val/2, by have := k.isLt; omega⟩

def numeratorBasisRight (d : ℕ) (k : Fin (2*d+1)) : Index d :=
  ⟨(k.val+1)/2, by have := k.isLt; omega⟩

theorem numeratorBasis_order (d : ℕ) (k : Fin (2*d+1)) :
    numeratorBasisLeft d k ≤ numeratorBasisRight d k := by
  change k.val/2 ≤ (k.val+1)/2
  omega

theorem numeratorBasis_sum (d : ℕ) (k : Fin (2*d+1)) :
    (numeratorBasisLeft d k).val+(numeratorBasisRight d k).val = k.val := by
  change k.val/2+(k.val+1)/2 = k.val
  omega

/-- The monomial right inverse uses only the diagonal and adjacent off-diagonal. -/
def numeratorBasisMatrix (d : ℕ) (k : Fin (2*d+1)) : Parameter d :=
  if h : numeratorBasisLeft d k = numeratorBasisRight d k then
    Pi.single ⟨(numeratorBasisLeft d k,numeratorBasisLeft d k), le_rfl⟩ 1
  else Pi.single ⟨(numeratorBasisLeft d k,numeratorBasisRight d k), numeratorBasis_order d k⟩ (1/2)

theorem affineNumerator_basis (d : ℕ) (k : Fin (2*d+1)) :
    affineNumerator (numeratorBasisMatrix d k) = X^k.val := by
  classical
  have hsum := numeratorBasis_sum d k
  by_cases heq : numeratorBasisLeft d k = numeratorBasisRight d k
  · rw [numeratorBasisMatrix, dif_pos heq, affineNumerator_single_diagonal]
    simp only [map_one, one_mul]
    congr 1
    rw [← heq] at hsum
    omega
  · rw [numeratorBasisMatrix, dif_neg heq,
      affineNumerator_single_offdiagonal _ _ (lt_of_le_of_ne (numeratorBasis_order d k) heq)]
    have hc : (2 : Polynomial ℂ)*C (1/2 : ℂ) = 1 := by
      change C (2 : ℂ)*C (1/2 : ℂ) = 1
      rw [← map_mul]
      norm_num
    rw [hc, one_mul, hsum]

def numeratorLift (d : ℕ) (c : Fin (2*d+1) → ℂ) : Parameter d :=
  ∑ k, c k • numeratorBasisMatrix d k

theorem affineNumerator_lift (d : ℕ) (c : Fin (2*d+1) → ℂ) :
    affineNumerator (numeratorLift d c) = ∑ k, C (c k)*X^k.val := by
  change affineNumeratorLinear d (∑ k, c k • numeratorBasisMatrix d k) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul]
  change c k • affineNumerator (numeratorBasisMatrix d k) = _
  rw [affineNumerator_basis, Polynomial.smul_eq_C_mul]

def numeratorCoefficientMap (d : ℕ) : Parameter d →ₗ[ℂ] (Fin (2*d+1) → ℂ) :=
  (Polynomial.toFn (2*d+1)).comp (affineNumeratorLinear d)

theorem numeratorCoefficientMap_lift (d : ℕ) (c : Fin (2*d+1) → ℂ) :
    numeratorCoefficientMap d (numeratorLift d c) = c := by
  classical
  ext k
  change (affineNumerator (numeratorLift d c)).coeff k.val = c k
  rw [affineNumerator_lift]
  simp only [finset_sum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    have hne : j.val ≠ k.val := fun h => hj (Fin.ext h)
    simp [hne, Ne.symm hne]
  · simp

theorem numeratorCoefficientMap_surjective (d : ℕ) :
    Function.Surjective (numeratorCoefficientMap d) :=
  fun c => ⟨numeratorLift d c, numeratorCoefficientMap_lift d c⟩

theorem affineNumerator_natDegree_le {d : ℕ} (H : Parameter d) :
    (affineNumerator H).natDegree ≤ 2*d := by
  change (affineNumeratorOver H).natDegree ≤ 2*d
  unfold affineNumeratorOver
  apply natDegree_sum_le_of_forall_le
  intro i _
  apply natDegree_sum_le_of_forall_le
  intro j _
  apply (natDegree_C_mul_X_pow_le _ _).trans
  have hi := i.isLt
  have hj := j.isLt
  omega

theorem affineNumerator_surjective_degreeLE (d : ℕ) (P : Polynomial ℂ)
    (hP : P.natDegree ≤ 2*d) : ∃ H : Parameter d, affineNumerator H = P := by
  let c : Fin (2*d+1) → ℂ := fun k => P.coeff k.val
  refine ⟨numeratorLift d c, ?_⟩
  have hcoeff := numeratorCoefficientMap_lift d c
  ext k
  by_cases hk : k < 2*d+1
  · exact congrFun hcoeff ⟨k,hk⟩
  · rw [coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt]
    · omega
    · have := affineNumerator_natDegree_le (numeratorLift d c)
      omega

#assert_trust kernel affineNumerator_single_diagonal
#assert_trust kernel affineNumerator_single_offdiagonal
#assert_trust kernel numeratorCoefficientMap_surjective
#assert_trust kernel affineNumerator_surjective_degreeLE
#print axioms affineNumerator_single_offdiagonal
#print axioms numeratorCoefficientMap_surjective
end NLA.Proofs.TR26
