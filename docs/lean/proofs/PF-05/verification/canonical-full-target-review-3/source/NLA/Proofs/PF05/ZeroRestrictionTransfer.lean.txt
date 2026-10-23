import NLA.Proofs.PF05.ZeroRestriction

/-! Exact restriction/restoration of factorizations and the two frozen PF05
properties, using the actual forced zero factors and directions at rank three. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05
namespace ZeroRestriction
open NLA.Statements.PF05
noncomputable section

private theorem zero_psd : PositiveSemidefinite (0:M2) := by
  refine ⟨?_,?_⟩
  · intro i j; rfl
  · intro x; simp

theorem extend_psd {n r : ℕ} {X : Fin n → M2} (c : Selection n r X)
    (Y : Fin r → M2) (hY : ∀ a, PositiveSemidefinite (Y a)) :
    ∀ i, PositiveSemidefinite (extend c Y i) := by
  intro i
  by_cases hi : X i=0
  · rw [extend_of_zero c Y i hi]; exact zero_psd
  · rw [extend_of_ne_zero c Y i hi]; exact hY _

theorem extend_symmetric {n r : ℕ} {X : Fin n → M2} (c : Selection n r X)
    (Y : Fin r → M2) (hY : ∀ a, Symmetric (Y a)) :
    ∀ i, Symmetric (extend c Y i) := by
  intro i
  by_cases hi : X i=0
  · rw [extend_of_zero c Y i hi]; exact zero_psd.1
  · rw [extend_of_ne_zero c Y i hi]; exact hY _

theorem extend_add_smul {n r : ℕ} {X : Fin n → M2} (c : Selection n r X)
    (Y Z : Fin r → M2) (t : ℝ) (i : Fin n) :
    extend c Y i+t • extend c Z i=extend c (fun a => Y a+t • Z a) i := by
  by_cases hi : X i=0 <;> simp [extend,hi]

/-- A pointwise identity on the actual retained core extends whenever the
other family has the same forced zero positions. -/
theorem eq_map_of_restricted_eq {n r : ℕ} {X Y : Fin n → M2}
    (c : Selection n r X) (f : M2 → M2) (hf : f 0=0)
    (hzero : ∀ i, X i=0 → Y i=0)
    (hcore : ∀ a, Y (c.pick a)=f (X (c.pick a))) : ∀ i, Y i=f (X i) := by
  intro i
  by_cases hi : X i=0
  · rw [hzero i hi,hi,hf]
  · obtain ⟨a,ha⟩ := c.covers i hi
    rw [← ha]; exact hcore a

theorem factorization_extend {p q r s : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → M2) (B : Fin q → M2)
    (cA : Selection p r A) (cB : Selection q s B) (hbase : Factorization M A B)
    (Ar : Fin r → M2) (Br : Fin s → M2)
    (hred : Factorization (reducedMatrix M cA cB) Ar Br) :
    Factorization M (extend cA Ar) (extend cB Br) := by
  refine ⟨extend_psd cA Ar hred.1,extend_psd cB Br hred.2.1,?_⟩
  intro i j
  by_cases hi : A i=0
  · rw [hbase.2.2 i j,hi,extend_of_zero cA Ar i hi]; simp
  by_cases hj : B j=0
  · rw [hbase.2.2 i j,hj,extend_of_zero cB Br j hj]; simp
  rw [extend_of_ne_zero cA Ar i hi,extend_of_ne_zero cB Br j hj]
  have he := hred.2.2 (lookup cA i hi) (lookup cB j hj)
  simpa [reducedMatrix,Matrix.submatrix_apply,pick_lookup] using he

theorem direction_restrict {p q r s : ℕ}
    (A E : Fin p → M2) (B F : Fin q → M2)
    (cA : Selection p r A) (cB : Selection q s B)
    (hdir : FeasibleDirection A E B F) :
    FeasibleDirection (reduced cA) (E ∘ cA.pick) (reduced cB) (F ∘ cB.pick) := by
  obtain ⟨hEs,hFs,ht,h,hh,hseg⟩ := hdir
  refine ⟨fun a => hEs (cA.pick a),fun b => hFs (cB.pick b),
    fun a b => ht (cA.pick a) (cB.pick b),h,hh,?_⟩
  intro t ht0 hth
  exact ⟨fun a => (hseg t ht0 hth).1 (cA.pick a),
    fun b => (hseg t ht0 hth).2 (cB.pick b)⟩

theorem direction_extend {p q r s : ℕ}
    {A : Fin p → M2} {B : Fin q → M2}
    (cA : Selection p r A) (cB : Selection q s B)
    (Ar Er : Fin r → M2) (Br Fr : Fin s → M2)
    (hred : FeasibleDirection Ar Er Br Fr) :
    FeasibleDirection (extend cA Ar) (extend cA Er) (extend cB Br) (extend cB Fr) := by
  obtain ⟨hEs,hFs,htrace,h,hh,hseg⟩ := hred
  refine ⟨extend_symmetric cA Er hEs,extend_symmetric cB Fr hFs,?_,h,hh,?_⟩
  · intro i j
    by_cases hi : A i=0
    · simp [extend,hi]
    by_cases hj : B j=0
    · simp [extend,hj]
    simpa [extend,hi,hj] using htrace (lookup cA i hi) (lookup cB j hj)
  · intro t ht hth
    refine ⟨?_,?_⟩
    · intro i
      rw [extend_add_smul]
      exact extend_psd cA _ (hseg t ht hth).1 i
    · intro j
      rw [extend_add_smul]
      exact extend_psd cB _ (hseg t ht hth).2 j

theorem rigid_reduced_of_full {p q r s : ℕ}
    {A : Fin p → M2} {B : Fin q → M2}
    (cA : Selection p r A) (cB : Selection q s B)
    (hfull : InfinitesimallyRigid A B) : InfinitesimallyRigid (reduced cA) (reduced cB) := by
  intro Er Fr hred
  have he := direction_extend cA cB (reduced cA) Er (reduced cB) Fr hred
  rw [extend_reduced,extend_reduced] at he
  obtain ⟨d,hdA,hdB⟩ := hfull _ _ he
  refine ⟨d,?_,?_⟩
  · intro a; simpa only [extend_pick,reduced,Function.comp_apply] using hdA (cA.pick a)
  · intro b; simpa only [extend_pick,reduced,Function.comp_apply] using hdB (cB.pick b)

theorem rigid_full_of_reduced {p q r s : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → M2) (B : Fin q → M2)
    (cA : Selection p r A) (cB : Selection q s B)
    (hbase : Factorization M A B) (hrank : M.rank=3)
    (hred : InfinitesimallyRigid (reduced cA) (reduced cB)) : InfinitesimallyRigid A B := by
  intro E F hdir
  obtain ⟨d,hdA,hdB⟩ := hred _ _ (direction_restrict A E B F cA cB hdir)
  refine ⟨d,?_,?_⟩
  · apply eq_map_of_restricted_eq cA (fun X => d • X) (by simp) ?_ hdA
    intro i hi
    apply feasible_zero_row M A E B F hbase hrank hdir i
    intro j; rw [hbase.2.2 i j,hi]; simp
  · apply eq_map_of_restricted_eq cB (fun X => (-d) • X) (by simp) ?_ hdB
    intro j hj
    apply feasible_zero_column M A E B F hbase hrank hdir j
    intro i; rw [hbase.2.2 i j,hj]; simp

theorem rigid_iff_reduced {p q r s : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → M2) (B : Fin q → M2)
    (cA : Selection p r A) (cB : Selection q s B)
    (hbase : Factorization M A B) (hrank : M.rank=3) :
    InfinitesimallyRigid A B ↔ InfinitesimallyRigid (reduced cA) (reduced cB) :=
  ⟨rigid_reduced_of_full cA cB,rigid_full_of_reduced M A B cA cB hbase hrank⟩

theorem unique_reduced_of_full {p q r s : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → M2) (B : Fin q → M2)
    (cA : Selection p r A) (cB : Selection q s B)
    (hbase : Factorization M A B) (hfull : UniqueUpToCongruence M A B) :
    UniqueUpToCongruence (reducedMatrix M cA cB) (reduced cA) (reduced cB) := by
  intro Ar Br hred
  obtain ⟨S,hS,hA,hB⟩ := hfull _ _ (factorization_extend M A B cA cB hbase Ar Br hred)
  refine ⟨S,hS,?_,?_⟩
  · intro a; simpa only [extend_pick,reduced,Function.comp_apply] using hA (cA.pick a)
  · intro b; simpa only [extend_pick,reduced,Function.comp_apply] using hB (cB.pick b)

theorem unique_full_of_reduced {p q r s : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → M2) (B : Fin q → M2)
    (cA : Selection p r A) (cB : Selection q s B)
    (hbase : Factorization M A B) (hrank : M.rank=3)
    (hred : UniqueUpToCongruence (reducedMatrix M cA cB) (reduced cA) (reduced cB)) :
    UniqueUpToCongruence M A B := by
  intro At Bt halt
  have hredalt : Factorization (reducedMatrix M cA cB) (At ∘ cA.pick) (Bt ∘ cB.pick) :=
    ⟨fun a => halt.1 (cA.pick a),fun b => halt.2.1 (cB.pick b),
      fun a b => halt.2.2 (cA.pick a) (cB.pick b)⟩
  obtain ⟨S,hS,hA,hB⟩ := hred _ _ hredalt
  refine ⟨S,hS,?_,?_⟩
  · apply eq_map_of_restricted_eq cA (fun X => S.transpose*X*S) (by simp) ?_ hA
    intro i hi
    apply factor_zero_row M At Bt halt hrank i
    intro j; rw [hbase.2.2 i j,hi]; simp
  · apply eq_map_of_restricted_eq cB (fun X => S⁻¹*X*(S⁻¹).transpose) (by simp) ?_ hB
    intro j hj
    apply factor_zero_column M At Bt halt hrank j
    intro i; rw [hbase.2.2 i j,hj]; simp

theorem unique_iff_reduced {p q r s : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → M2) (B : Fin q → M2)
    (cA : Selection p r A) (cB : Selection q s B)
    (hbase : Factorization M A B) (hrank : M.rank=3) :
    UniqueUpToCongruence M A B ↔
      UniqueUpToCongruence (reducedMatrix M cA cB) (reduced cA) (reduced cB) :=
  ⟨unique_reduced_of_full M A B cA cB hbase,unique_full_of_reduced M A B cA cB hbase hrank⟩

#assert_trust kernel factorization_extend
#assert_trust kernel direction_extend
#assert_trust kernel rigid_iff_reduced
#assert_trust kernel unique_iff_reduced
#print axioms unique_iff_reduced
end
end ZeroRestriction
end NLA.Proofs.PF05
