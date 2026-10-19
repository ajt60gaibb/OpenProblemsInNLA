import NLA.Proofs.PF05.Basic
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.Tactic

/-! Positive-ray compression for PF-05. This module constructs finite representative
families and proves algebraic transfer of the frozen target's two properties.
It does not prove the positive case. -/
set_option autoImplicit false

namespace NLA.Proofs.PF05
open NLA.Statements.PF05

abbrev Sym2 := Matrix (Fin 2) (Fin 2) ℝ

/-- An indexed family obtained by retaining representatives and multiplying them
by strictly positive scalars. `pick` names the retained factors. -/
structure RayCompression (n r : ℕ) (X : Fin n → Sym2) where
  rep : Fin n → Fin r
  pick : Fin r → Fin n
  scale : Fin n → ℝ
  scale_pos : ∀ i, 0 < scale i
  rep_pick : ∀ a, rep (pick a) = a
  scale_pick : ∀ a, scale (pick a) = 1
  reconstruct : ∀ i, X i = scale i • X (pick (rep i))

namespace RayCompression

def reduced {n r : ℕ} {X : Fin n → Sym2} (c : RayCompression n r X) : Fin r → Sym2 :=
  X ∘ c.pick

def extend {n r : ℕ} {X : Fin n → Sym2} (c : RayCompression n r X)
    (Y : Fin r → Sym2) : Fin n → Sym2 := fun i => c.scale i • Y (c.rep i)

@[simp] theorem reduced_apply {n r : ℕ} {X : Fin n → Sym2}
    (c : RayCompression n r X) (a : Fin r) : c.reduced a = X (c.pick a) := rfl

@[simp] theorem extend_apply_pick {n r : ℕ} {X : Fin n → Sym2}
    (c : RayCompression n r X) (Y : Fin r → Sym2) (a : Fin r) :
    c.extend Y (c.pick a) = Y a := by
  simp [extend, c.rep_pick, c.scale_pick]

theorem extend_reduced {n r : ℕ} {X : Fin n → Sym2}
    (c : RayCompression n r X) : c.extend c.reduced = X := by
  funext i
  exact (c.reconstruct i).symm

@[simp] theorem reconstruct_pick {n r : ℕ} {X : Fin n → Sym2}
    (c : RayCompression n r X) (a : Fin r) :
    c.scale (c.pick a) • c.reduced (c.rep (c.pick a)) = c.reduced a := by
  simp [c.rep_pick, c.scale_pick]

end RayCompression

def reducedMatrix {p q r s : ℕ} (M : Matrix (Fin p) (Fin q) ℝ)
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (cA : RayCompression p r A) (cB : RayCompression q s B) :
    Matrix (Fin r) (Fin s) ℝ := fun a b => M (cA.pick a) (cB.pick b)

def rowExpansion {p r : ℕ} {A : Fin p → Sym2}
    (cA : RayCompression p r A) : Matrix (Fin p) (Fin r) ℝ :=
  fun i a => if cA.rep i = a then cA.scale i else 0

def columnExpansion {q s : ℕ} {B : Fin q → Sym2}
    (cB : RayCompression q s B) : Matrix (Fin s) (Fin q) ℝ :=
  fun b j => if cB.rep j = b then cB.scale j else 0

private theorem trace_scaled (X Y : Sym2) (a b : ℝ) :
    Matrix.trace ((a • X) * (b • Y)) = a * b * Matrix.trace (X * Y) := by
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
  ring

theorem entry_reconstruct {p q r s : ℕ}
    {M : Matrix (Fin p) (Fin q) ℝ}
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (cA : RayCompression p r A) (cB : RayCompression q s B)
    (hfact : Factorization M A B) (i : Fin p) (j : Fin q) :
    M i j = cA.scale i * cB.scale j *
      reducedMatrix M cA cB (cA.rep i) (cB.rep j) := by
  rw [hfact.2.2 i j, cA.reconstruct i, cB.reconstruct j]
  rw [trace_scaled]
  rw [← hfact.2.2 (cA.pick (cA.rep i)) (cB.pick (cB.rep j))]
  rfl

theorem matrix_reconstruct {p q r s : ℕ}
    {M : Matrix (Fin p) (Fin q) ℝ}
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (cA : RayCompression p r A) (cB : RayCompression q s B)
    (hfact : Factorization M A B) :
    M = rowExpansion cA * reducedMatrix M cA cB * columnExpansion cB := by
  ext i j
  have hrow : ∀ b : Fin s,
      (rowExpansion cA * reducedMatrix M cA cB) i b =
        cA.scale i * reducedMatrix M cA cB (cA.rep i) b := by
    intro b
    simp [Matrix.mul_apply, rowExpansion]
  have hcol :
      (rowExpansion cA * reducedMatrix M cA cB * columnExpansion cB) i j =
        cA.scale i * cB.scale j *
          reducedMatrix M cA cB (cA.rep i) (cB.rep j) := by
    simp [Matrix.mul_apply, columnExpansion, hrow]
    ring
  exact (entry_reconstruct cA cB hfact i j).trans hcol.symm


theorem factorization_restrict {p q r s : ℕ}
    {M : Matrix (Fin p) (Fin q) ℝ}
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (cA : RayCompression p r A) (cB : RayCompression q s B)
    (hfact : Factorization M A B) :
    Factorization (reducedMatrix M cA cB) cA.reduced cB.reduced := by
  exact ⟨(fun a => hfact.1 (cA.pick a)),
    (fun b => hfact.2.1 (cB.pick b)),
    (fun a b => hfact.2.2 (cA.pick a) (cB.pick b))⟩

theorem reduced_rank_three {p q r s : ℕ}
    {M : Matrix (Fin p) (Fin q) ℝ}
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (cA : RayCompression p r A) (cB : RayCompression q s B)
    (hfact : Factorization M A B) (hrank : M.rank = 3) :
    (reducedMatrix M cA cB).rank = 3 := by
  have hlow : 3 ≤ (reducedMatrix M cA cB).rank := by
    calc
      3 = M.rank := hrank.symm
      _ = (rowExpansion cA * reducedMatrix M cA cB * columnExpansion cB).rank := by
        rw [← matrix_reconstruct cA cB hfact]
      _ ≤ (rowExpansion cA * reducedMatrix M cA cB).rank :=
        Matrix.rank_mul_le_left _ _
      _ ≤ (reducedMatrix M cA cB).rank := Matrix.rank_mul_le_right _ _
  have hredfact := factorization_restrict cA cB hfact
  have hhigh : (reducedMatrix M cA cB).rank ≤ 3 := by
    rw [factorization_coordinates (reducedMatrix M cA cB) cA.reduced cB.reduced hredfact]
    exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_le_height _)
  exact Nat.le_antisymm hhigh hlow

/-- A full-rank factor family has this property. The rank-three-to-separation
lemma is kept separate from the compression algebra. -/
def TraceSeparating {n : ℕ} (X : Fin n → Sym2) : Prop :=
  ∀ C : Sym2, Symmetric C → (∀ i, Matrix.trace (C * X i) = 0) → C = 0

theorem factorization_trace_separating {p q : ℕ}
    {M : Matrix (Fin p) (Fin q) ℝ}
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (hfact : Factorization M A B) (hrank : M.rank = 3) :
    TraceSeparating A ∧ TraceSeparating B := by
  constructor
  · intro C hCs horth
    apply trace_pairing_left_nondegenerate_of_rank_three M A B hfact hrank C hCs
    intro i
    rw [Matrix.trace_mul_comm]
    exact horth i
  · intro C hCs horth
    exact trace_pairing_right_nondegenerate_of_rank_three M A B hfact hrank C hCs horth

theorem row_relation {p q r : ℕ}
    {M : Matrix (Fin p) (Fin q) ℝ}
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (cA : RayCompression p r A) (hfact : Factorization M A B)
    (i : Fin p) (j : Fin q) :
    M i j = cA.scale i * M (cA.pick (cA.rep i)) j := by
  rw [hfact.2.2 i j, cA.reconstruct i]
  rw [hfact.2.2 (cA.pick (cA.rep i)) j]
  simp [Matrix.trace_smul]

theorem column_relation {p q s : ℕ}
    {M : Matrix (Fin p) (Fin q) ℝ}
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (cB : RayCompression q s B) (hfact : Factorization M A B)
    (i : Fin p) (j : Fin q) :
    M i j = cB.scale j * M i (cB.pick (cB.rep j)) := by
  rw [hfact.2.2 i j, cB.reconstruct j]
  rw [hfact.2.2 i (cB.pick (cB.rep j))]
  simp [Matrix.trace_smul]

theorem alternative_row_relation {p q r : ℕ}
    {M : Matrix (Fin p) (Fin q) ℝ}
    {A At : Fin p → Sym2} {B Bt : Fin q → Sym2}
    (cA : RayCompression p r A)
    (hbase : Factorization M A B) (halt : Factorization M At Bt)
    (hsep : TraceSeparating Bt) (i : Fin p) :
    At i = cA.scale i • At (cA.pick (cA.rep i)) := by
  let C : Sym2 := At i - cA.scale i • At (cA.pick (cA.rep i))
  have hCs : Symmetric C := by
    intro a b
    simp [C, Matrix.sub_apply, Matrix.smul_apply,
      (halt.1 i).1 a b, (halt.1 (cA.pick (cA.rep i))).1 a b]
  have hCt : ∀ j, Matrix.trace (C * Bt j) = 0 := by
    intro j
    have hr := row_relation cA hbase i j
    simp only [C, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub,
      Matrix.trace_smul, smul_eq_mul]
    rw [halt.2.2 i j, halt.2.2 (cA.pick (cA.rep i)) j] at hr
    linarith
  have hz := hsep C hCs hCt
  dsimp [C] at hz
  exact sub_eq_zero.mp hz

theorem alternative_column_relation {p q s : ℕ}
    {M : Matrix (Fin p) (Fin q) ℝ}
    {A At : Fin p → Sym2} {B Bt : Fin q → Sym2}
    (cB : RayCompression q s B)
    (hbase : Factorization M A B) (halt : Factorization M At Bt)
    (hsep : TraceSeparating At) (j : Fin q) :
    Bt j = cB.scale j • Bt (cB.pick (cB.rep j)) := by
  let C : Sym2 := Bt j - cB.scale j • Bt (cB.pick (cB.rep j))
  have hCs : Symmetric C := by
    intro a b
    simp [C, Matrix.sub_apply, Matrix.smul_apply,
      (halt.2.1 j).1 a b, (halt.2.1 (cB.pick (cB.rep j))).1 a b]
  have hCt : ∀ i, Matrix.trace (C * At i) = 0 := by
    intro i
    have hr := column_relation cB hbase i j
    rw [halt.2.2 i j, halt.2.2 i (cB.pick (cB.rep j))] at hr
    rw [Matrix.trace_mul_comm]
    simp only [C, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub,
      Matrix.trace_smul, smul_eq_mul]
    linarith
  have hz := hsep C hCs hCt
  dsimp [C] at hz
  exact sub_eq_zero.mp hz

theorem direction_row_relation {p q r : ℕ}
    {A E : Fin p → Sym2} {B F : Fin q → Sym2}
    (cA : RayCompression p r A)
    (hdir : FeasibleDirection A E B F)
    (hsep : TraceSeparating B) (i : Fin p) :
    E i = cA.scale i • E (cA.pick (cA.rep i)) := by
  let C : Sym2 := E i - cA.scale i • E (cA.pick (cA.rep i))
  have hCs : Symmetric C := by
    intro a b
    simp [C, Matrix.sub_apply, Matrix.smul_apply,
      hdir.1 i a b, hdir.1 (cA.pick (cA.rep i)) a b]
  have hCt : ∀ j, Matrix.trace (C * B j) = 0 := by
    intro j
    have hi := hdir.2.2.1 i j
    have hk := hdir.2.2.1 (cA.pick (cA.rep i)) j
    rw [cA.reconstruct i] at hi
    simp only [C, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub,
      Matrix.trace_smul, smul_eq_mul]
    simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at hi
    have hks := congrArg (fun z : ℝ => cA.scale i * z) hk
    nlinarith [hks]
  have hz := hsep C hCs hCt
  dsimp [C] at hz
  exact sub_eq_zero.mp hz

theorem direction_column_relation {p q s : ℕ}
    {A E : Fin p → Sym2} {B F : Fin q → Sym2}
    (cB : RayCompression q s B)
    (hdir : FeasibleDirection A E B F)
    (hsep : TraceSeparating A) (j : Fin q) :
    F j = cB.scale j • F (cB.pick (cB.rep j)) := by
  let C : Sym2 := F j - cB.scale j • F (cB.pick (cB.rep j))
  have hCs : Symmetric C := by
    intro a b
    simp [C, Matrix.sub_apply, Matrix.smul_apply,
      hdir.2.1 j a b, hdir.2.1 (cB.pick (cB.rep j)) a b]
  have hCt : ∀ i, Matrix.trace (C * A i) = 0 := by
    intro i
    have hj := hdir.2.2.1 i j
    have hk := hdir.2.2.1 i (cB.pick (cB.rep j))
    rw [cB.reconstruct j] at hj
    rw [Matrix.trace_mul_comm]
    simp only [C, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub,
      Matrix.trace_smul, smul_eq_mul]
    simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at hj
    have hks := congrArg (fun z : ℝ => cB.scale j * z) hk
    nlinarith [hks]
  have hz := hsep C hCs hCt
  dsimp [C] at hz
  exact sub_eq_zero.mp hz

theorem psd_smul_of_nonneg (X : Sym2) (hX : PositiveSemidefinite X)
    (a : ℝ) (ha : 0 ≤ a) : PositiveSemidefinite (a • X) := by
  constructor
  · intro i j
    simp [Matrix.smul_apply, hX.1 i j]
  · intro x
    have h := hX.2 x
    have hq : (∑ i, ∑ j, x i * (a • X) i j * x j) =
        a * (∑ i, ∑ j, x i * X i j * x j) := by
      simp [Matrix.smul_apply, Fin.sum_univ_two, smul_eq_mul]
      ring
    rw [hq]
    exact mul_nonneg ha h

theorem factorization_extend {p q r s : ℕ}
    {M : Matrix (Fin p) (Fin q) ℝ}
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (cA : RayCompression p r A) (cB : RayCompression q s B)
    {Ar : Fin r → Sym2} {Br : Fin s → Sym2}
    (hM : ∀ i j, M i j = cA.scale i * cB.scale j *
      reducedMatrix M cA cB (cA.rep i) (cB.rep j))
    (hred : Factorization (reducedMatrix M cA cB) Ar Br) :
    Factorization M (cA.extend Ar) (cB.extend Br) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact psd_smul_of_nonneg _ (hred.1 (cA.rep i)) _ (le_of_lt (cA.scale_pos i))
  · intro j
    exact psd_smul_of_nonneg _ (hred.2.1 (cB.rep j)) _ (le_of_lt (cB.scale_pos j))
  · intro i j
    rw [hM i j, hred.2.2 (cA.rep i) (cB.rep j)]
    exact (trace_scaled _ _ _ _).symm

theorem direction_extend {p q r s : ℕ}
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (cA : RayCompression p r A) (cB : RayCompression q s B)
    {Ar Er : Fin r → Sym2} {Br Fr : Fin s → Sym2}
    (hred : FeasibleDirection Ar Er Br Fr) :
    FeasibleDirection (cA.extend Ar) (cA.extend Er)
      (cB.extend Br) (cB.extend Fr) := by
  rcases hred with ⟨hEs, hFs, htrace, h, hh, hseg⟩
  refine ⟨?_, ?_, ?_, ⟨h, hh, ?_⟩⟩
  · intro i a b
    simp [RayCompression.extend, Matrix.smul_apply, hEs (cA.rep i) a b]
  · intro j a b
    simp [RayCompression.extend, Matrix.smul_apply, hFs (cB.rep j) a b]
  · intro i j
    change Matrix.trace (((cA.scale i • Er (cA.rep i)) *
        (cB.scale j • Br (cB.rep j)))) +
      Matrix.trace (((cA.scale i • Ar (cA.rep i)) *
        (cB.scale j • Fr (cB.rep j)))) = 0
    rw [trace_scaled, trace_scaled]
    calc
      cA.scale i * cB.scale j * Matrix.trace (Er (cA.rep i) * Br (cB.rep j)) +
          cA.scale i * cB.scale j * Matrix.trace (Ar (cA.rep i) * Fr (cB.rep j)) =
        cA.scale i * cB.scale j *
          (Matrix.trace (Er (cA.rep i) * Br (cB.rep j)) +
            Matrix.trace (Ar (cA.rep i) * Fr (cB.rep j))) := by ring
      _ = 0 := by rw [htrace (cA.rep i) (cB.rep j)]; ring
  · intro t ht hth
    obtain ⟨hAp, hBp⟩ := hseg t ht hth
    constructor
    · intro i
      have hp := psd_smul_of_nonneg
        (Ar (cA.rep i) + t • Er (cA.rep i)) (hAp (cA.rep i))
        (cA.scale i) (le_of_lt (cA.scale_pos i))
      simpa [RayCompression.extend, smul_add, smul_smul, mul_comm] using hp
    · intro j
      have hp := psd_smul_of_nonneg
        (Br (cB.rep j) + t • Fr (cB.rep j)) (hBp (cB.rep j))
        (cB.scale j) (le_of_lt (cB.scale_pos j))
      simpa [RayCompression.extend, smul_add, smul_smul, mul_comm] using hp

theorem direction_restrict {p q r s : ℕ}
    {A E : Fin p → Sym2} {B F : Fin q → Sym2}
    (cA : RayCompression p r A) (cB : RayCompression q s B)
    (hdir : FeasibleDirection A E B F) :
    FeasibleDirection cA.reduced (E ∘ cA.pick)
      cB.reduced (F ∘ cB.pick) := by
  rcases hdir with ⟨hEs, hFs, htrace, h, hh, hseg⟩
  refine ⟨(fun a => hEs (cA.pick a)), (fun b => hFs (cB.pick b)),
    (fun a b => htrace (cA.pick a) (cB.pick b)), ⟨h, hh, ?_⟩⟩
  intro t ht hth
  obtain ⟨hAp, hBp⟩ := hseg t ht hth
  exact ⟨(fun a => hAp (cA.pick a)), (fun b => hBp (cB.pick b))⟩

theorem rigid_full_of_reduced {p q r s : ℕ}
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (cA : RayCompression p r A) (cB : RayCompression q s B)
    (hsepA : TraceSeparating A) (hsepB : TraceSeparating B)
    (hred : InfinitesimallyRigid cA.reduced cB.reduced) :
    InfinitesimallyRigid A B := by
  intro E F hdir
  have hdirred := direction_restrict cA cB hdir
  obtain ⟨d, hdA, hdB⟩ := hred _ _ hdirred
  refine ⟨d, ?_, ?_⟩
  · intro i
    have ha := hdA (cA.rep i)
    change E (cA.pick (cA.rep i)) =
      d • A (cA.pick (cA.rep i)) at ha
    rw [direction_row_relation cA hdir hsepB i, ha, cA.reconstruct i]
    simp [smul_smul, mul_comm]
  · intro j
    have hb := hdB (cB.rep j)
    change F (cB.pick (cB.rep j)) =
      (-d) • B (cB.pick (cB.rep j)) at hb
    rw [direction_column_relation cB hdir hsepA j, hb, cB.reconstruct j]
    simp [smul_smul, mul_comm]

theorem rigid_reduced_of_full {p q r s : ℕ}
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (cA : RayCompression p r A) (cB : RayCompression q s B)
    (hfull : InfinitesimallyRigid A B) :
    InfinitesimallyRigid cA.reduced cB.reduced := by
  intro Er Fr hred
  have hdir := direction_extend cA cB hred
  rw [cA.extend_reduced, cB.extend_reduced] at hdir
  obtain ⟨d, hdA, hdB⟩ := hfull _ _ hdir
  refine ⟨d, ?_, ?_⟩
  · intro a
    simpa only [cA.extend_apply_pick, RayCompression.reduced_apply] using
      hdA (cA.pick a)
  · intro b
    simpa only [cB.extend_apply_pick, RayCompression.reduced_apply] using
      hdB (cB.pick b)

theorem rigid_iff_reduced {p q r s : ℕ}
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (cA : RayCompression p r A) (cB : RayCompression q s B)
    (hsepA : TraceSeparating A) (hsepB : TraceSeparating B) :
    InfinitesimallyRigid A B ↔
      InfinitesimallyRigid cA.reduced cB.reduced := by
  exact ⟨rigid_reduced_of_full cA cB,
    rigid_full_of_reduced cA cB hsepA hsepB⟩

theorem unique_reduced_of_full {p q r s : ℕ}
    {M : Matrix (Fin p) (Fin q) ℝ}
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (cA : RayCompression p r A) (cB : RayCompression q s B)
    (hfact : Factorization M A B)
    (hfull : UniqueUpToCongruence M A B) :
    UniqueUpToCongruence (reducedMatrix M cA cB) cA.reduced cB.reduced := by
  intro Ar Br hred
  have hnew := factorization_extend cA cB
    (fun i j => entry_reconstruct cA cB hfact i j) hred
  obtain ⟨S, hS, hA, hB⟩ := hfull _ _ hnew
  refine ⟨S, hS, ?_, ?_⟩
  · intro a
    simpa only [cA.extend_apply_pick, RayCompression.reduced_apply] using
      hA (cA.pick a)
  · intro b
    simpa only [cB.extend_apply_pick, RayCompression.reduced_apply] using
      hB (cB.pick b)

theorem unique_full_of_reduced {p q r s : ℕ}
    {M : Matrix (Fin p) (Fin q) ℝ}
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (cA : RayCompression p r A) (cB : RayCompression q s B)
    (hbase : Factorization M A B)
    (hseparating : ∀ At : Fin p → Sym2, ∀ Bt : Fin q → Sym2,
      Factorization M At Bt → TraceSeparating At ∧ TraceSeparating Bt)
    (hred : UniqueUpToCongruence (reducedMatrix M cA cB)
      cA.reduced cB.reduced) :
    UniqueUpToCongruence M A B := by
  intro At Bt halt
  obtain ⟨hsepA, hsepB⟩ := hseparating At Bt halt
  have haltred : Factorization (reducedMatrix M cA cB)
      (At ∘ cA.pick) (Bt ∘ cB.pick) :=
    ⟨(fun a => halt.1 (cA.pick a)),
      (fun b => halt.2.1 (cB.pick b)),
      (fun a b => halt.2.2 (cA.pick a) (cB.pick b))⟩
  obtain ⟨S, hS, hA, hB⟩ := hred _ _ haltred
  refine ⟨S, hS, ?_, ?_⟩
  · intro i
    have ha := hA (cA.rep i)
    change At (cA.pick (cA.rep i)) =
      S.transpose * A (cA.pick (cA.rep i)) * S at ha
    rw [alternative_row_relation cA hbase halt hsepB i,
      ha, cA.reconstruct i]
    simp
  · intro j
    have hb := hB (cB.rep j)
    change Bt (cB.pick (cB.rep j)) =
      S⁻¹ * B (cB.pick (cB.rep j)) * (S⁻¹).transpose at hb
    rw [alternative_column_relation cB hbase halt hsepA j,
      hb, cB.reconstruct j]
    simp

theorem unique_iff_reduced {p q r s : ℕ}
    {M : Matrix (Fin p) (Fin q) ℝ}
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (cA : RayCompression p r A) (cB : RayCompression q s B)
    (hbase : Factorization M A B)
    (hseparating : ∀ At : Fin p → Sym2, ∀ Bt : Fin q → Sym2,
      Factorization M At Bt → TraceSeparating At ∧ TraceSeparating Bt) :
    UniqueUpToCongruence M A B ↔
      UniqueUpToCongruence (reducedMatrix M cA cB)
        cA.reduced cB.reduced := by
  exact ⟨unique_reduced_of_full cA cB hbase,
    unique_full_of_reduced cA cB hbase hseparating⟩

/-- Compression by positive rays preserves both parts of the PF-05 target
when the original matrix has ordinary rank three. The construction of a
compression with distinct rank-one rays is a separate obligation. -/
theorem rigidity_and_uniqueness_iff_reduced_of_rank_three {p q r s : ℕ}
    {M : Matrix (Fin p) (Fin q) ℝ}
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (cA : RayCompression p r A) (cB : RayCompression q s B)
    (hbase : Factorization M A B) (hrank : M.rank = 3) :
    (InfinitesimallyRigid A B ↔
      InfinitesimallyRigid cA.reduced cB.reduced) ∧
    (UniqueUpToCongruence M A B ↔
      UniqueUpToCongruence (reducedMatrix M cA cB)
        cA.reduced cB.reduced) := by
  obtain ⟨hsepA, hsepB⟩ := factorization_trace_separating hbase hrank
  constructor
  · exact rigid_iff_reduced cA cB hsepA hsepB
  · apply unique_iff_reduced cA cB hbase
    intro At Bt halt
    exact factorization_trace_separating halt hrank

/-- Positive proportionality of two symmetric factors. The zero factor forms
one class, so this relation is an equivalence without nonzero assumptions. -/
def SamePositiveRay (X Y : Sym2) : Prop :=
  ∃ c : ℝ, 0 < c ∧ X = c • Y

theorem samePositiveRay_refl (X : Sym2) : SamePositiveRay X X := by
  exact ⟨1, by norm_num, by simp⟩

theorem samePositiveRay_symm {X Y : Sym2} :
    SamePositiveRay X Y → SamePositiveRay Y X := by
  rintro ⟨c, hc, hXY⟩
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  rw [hXY]
  simp [smul_smul, ne_of_gt hc]

theorem samePositiveRay_trans {X Y Z : Sym2} :
    SamePositiveRay X Y → SamePositiveRay Y Z → SamePositiveRay X Z := by
  rintro ⟨c, hc, hXY⟩ ⟨d, hd, hYZ⟩
  refine ⟨c * d, mul_pos hc hd, ?_⟩
  rw [hXY, hYZ]
  simp [smul_smul]

def positiveRaySetoid {n : ℕ} (X : Fin n → Sym2) : Setoid (Fin n) where
  r i j := SamePositiveRay (X i) (X j)
  iseqv := {
    refl := fun i => samePositiveRay_refl (X i)
    symm := fun h => samePositiveRay_symm h
    trans := fun h₁ h₂ => samePositiveRay_trans h₁ h₂ }

set_option linter.style.haveILetI false in
/-- Every finite factor family admits a finite positive-ray compression.
The retained factors represent distinct positive rays. -/
theorem exists_distinct_positive_ray_compression {n : ℕ} (X : Fin n → Sym2) :
    ∃ r : ℕ, ∃ c : RayCompression n r X,
      ∀ a b : Fin r, SamePositiveRay (c.reduced a) (c.reduced b) → a = b := by
  classical
  let s := positiveRaySetoid X
  let Q := Quotient s
  letI : Finite Q := Finite.of_surjective (Quotient.mk s) Quotient.mk_surjective
  letI : Fintype Q := Fintype.ofFinite Q
  let e : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let rep : Fin n → Fin (Fintype.card Q) := fun i => e ⟦i⟧
  let pick : Fin (Fintype.card Q) → Fin n := fun a => (e.symm a).out
  have hrep_pick : ∀ a, rep (pick a) = a := by
    intro a
    change e ⟦(e.symm a).out⟧ = a
    rw [Quotient.out_eq]
    simp
  have hsame : ∀ i, SamePositiveRay (X i) (X (pick (rep i))) := by
    intro i
    change SamePositiveRay (X i) (X ((e.symm (e ⟦i⟧)).out))
    simp only [e.symm_apply_apply]
    exact samePositiveRay_symm (Quotient.mk_out i)
  let scale : Fin n → ℝ := fun i =>
    if hi : i = pick (rep i) then 1 else Classical.choose (hsame i)
  have hscale_pos : ∀ i, 0 < scale i := by
    intro i
    dsimp [scale]
    split_ifs with hi
    · norm_num
    · exact (Classical.choose_spec (hsame i)).1
  have hscale_pick : ∀ a, scale (pick a) = 1 := by
    intro a
    have hp : pick a = pick (rep (pick a)) := by rw [hrep_pick]
    exact dif_pos hp
  have hreconstruct : ∀ i, X i = scale i • X (pick (rep i)) := by
    intro i
    dsimp [scale]
    split_ifs with hi
    · simpa only [one_smul] using congrArg X hi
    · exact (Classical.choose_spec (hsame i)).2
  let c : RayCompression n (Fintype.card Q) X :=
    { rep := rep
      pick := pick
      scale := scale
      scale_pos := hscale_pos
      rep_pick := hrep_pick
      scale_pick := hscale_pick
      reconstruct := hreconstruct }
  refine ⟨Fintype.card Q, c, ?_⟩
  intro a b hab
  have hq : (⟦pick a⟧ : Q) = ⟦pick b⟧ := Quotient.sound hab
  have he := congrArg e hq
  simpa [rep, hrep_pick] using he

/-- For a strictly positive rank-three matrix, remove every repeated positive
factor ray on both sides. The reduced problem stays strictly positive and
rank three, and both exact PF-05 properties are unchanged. -/
theorem exists_positive_reduction {p q : ℕ}
    {M : Matrix (Fin p) (Fin q) ℝ}
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (hfact : Factorization M A B) (hrank : M.rank = 3)
    (hpos : ∀ i j, 0 < M i j) :
    ∃ r s : ℕ, ∃ cA : RayCompression p r A,
      ∃ cB : RayCompression q s B,
      (∀ a b, 0 < reducedMatrix M cA cB a b) ∧
      (reducedMatrix M cA cB).rank = 3 ∧
      Factorization (reducedMatrix M cA cB) cA.reduced cB.reduced ∧
      (∀ a b, SamePositiveRay (cA.reduced a) (cA.reduced b) → a = b) ∧
      (∀ a b, SamePositiveRay (cB.reduced a) (cB.reduced b) → a = b) ∧
      (InfinitesimallyRigid A B ↔
        InfinitesimallyRigid cA.reduced cB.reduced) ∧
      (UniqueUpToCongruence M A B ↔
        UniqueUpToCongruence (reducedMatrix M cA cB)
          cA.reduced cB.reduced) := by
  obtain ⟨r, cA, hA⟩ := exists_distinct_positive_ray_compression A
  obtain ⟨s, cB, hB⟩ := exists_distinct_positive_ray_compression B
  obtain ⟨hrigid, hunique⟩ :=
    rigidity_and_uniqueness_iff_reduced_of_rank_three cA cB hfact hrank
  exact ⟨r, s, cA, cB,
    (fun a b => hpos (cA.pick a) (cB.pick b)),
    reduced_rank_three cA cB hfact hrank,
    factorization_restrict cA cB hfact,
    hA, hB, hrigid, hunique⟩

/-! The next lemmas bridge matrix-ray distinctness to the pairwise vector
independence used by Dawson et al. for rank-one outer-product factors. -/

abbrev Vec2 := Fin 2 → ℝ

def outer (v : Vec2) : Sym2 := Matrix.vecMulVec v v

def cross (v w : Vec2) : ℝ := v 0 * w 1 - v 1 * w 0

def pairMatrix (v w : Vec2) : Sym2 :=
  fun i j => if j = 0 then v i else w i

theorem outer_smul (v : Vec2) (c : ℝ) :
    outer (c • v) = c ^ 2 • outer v := by
  ext i j
  simp [outer, Matrix.vecMulVec_apply, smul_eq_mul]
  ring

theorem exists_smul_of_cross_eq_zero {v w : Vec2}
    (hv : v ≠ 0) (hw : w ≠ 0) (hcross : cross v w = 0) :
    ∃ c : ℝ, c ≠ 0 ∧ v = c • w := by
  have vector_eq_zero (u : Vec2) (h0 : u 0 = 0) (h1 : u 1 = 0) : u = 0 := by
    funext i
    fin_cases i <;> simp [h0, h1]
  by_cases hw0 : w 0 = 0
  · have hw1 : w 1 ≠ 0 := by
      intro h
      exact hw (vector_eq_zero w hw0 h)
    have hv0 : v 0 = 0 := by
      dsimp [cross] at hcross
      rw [hw0, mul_zero, sub_zero] at hcross
      exact (mul_eq_zero.mp hcross).resolve_right hw1
    have hv1 : v 1 ≠ 0 := by
      intro h
      exact hv (vector_eq_zero v hv0 h)
    refine ⟨v 1 / w 1, div_ne_zero hv1 hw1, ?_⟩
    funext i
    fin_cases i
    · simp [smul_eq_mul, hw0, hv0]
    · simp [smul_eq_mul, div_mul_cancel₀ _ hw1]
  · have hv0 : v 0 ≠ 0 := by
      intro h
      have hv1 : v 1 = 0 := by
        dsimp [cross] at hcross
        rw [h, zero_mul, zero_sub, neg_eq_zero] at hcross
        exact (mul_eq_zero.mp hcross).resolve_right hw0
      exact hv (vector_eq_zero v h hv1)
    refine ⟨v 0 / w 0, div_ne_zero hv0 hw0, ?_⟩
    funext i
    fin_cases i
    · simp [smul_eq_mul, div_mul_cancel₀ _ hw0]
    · simp only [Pi.smul_apply, smul_eq_mul]
      dsimp [cross] at hcross
      have hmul : v 1 * w 0 = v 0 * w 1 := by linarith [hcross]
      field_simp [hw0]
      exact hmul

theorem samePositiveRay_outer_of_cross_eq_zero {v w : Vec2}
    (hv : v ≠ 0) (hw : w ≠ 0) (hcross : cross v w = 0) :
    SamePositiveRay (outer v) (outer w) := by
  obtain ⟨c, hc, rfl⟩ := exists_smul_of_cross_eq_zero hv hw hcross
  exact ⟨c ^ 2, sq_pos_of_ne_zero hc, outer_smul w c⟩

theorem cross_ne_zero_of_outer_distinct {v w : Vec2}
    (hv : v ≠ 0) (hw : w ≠ 0)
    (hdistinct : ¬ SamePositiveRay (outer v) (outer w)) :
    cross v w ≠ 0 := by
  intro hcross
  exact hdistinct (samePositiveRay_outer_of_cross_eq_zero hv hw hcross)

theorem pairMatrix_det (v w : Vec2) :
    (pairMatrix v w).det = cross v w := by
  simp [pairMatrix, cross, Matrix.det_fin_two]
  ring

/-- Distinct positive rays of nonzero rank-one PSD outer products have
linearly independent generating vectors. -/
theorem linearIndependent_of_outer_distinct {v w : Vec2}
    (hv : v ≠ 0) (hw : w ≠ 0)
    (hdistinct : ¬ SamePositiveRay (outer v) (outer w)) :
    LinearIndependent ℝ (fun j : Fin 2 => if j = 0 then v else w) := by
  have hdet : (pairMatrix v w).det ≠ 0 := by
    rw [pairMatrix_det]
    exact cross_ne_zero_of_outer_distinct hv hw hdistinct
  have hli := Matrix.Nonsingular.linearIndependent_col
    (Matrix.nonsingular_iff_det_ne_zero.mpr hdet)
  have hcol : (pairMatrix v w).col =
      (fun j : Fin 2 => if j = 0 then v else w) := by
    funext j i
    by_cases hj : j = 0 <;> simp [Matrix.col, pairMatrix, hj]
  rwa [hcol] at hli

/-- A singular real PSD matrix of size two is an outer product. -/
theorem outer_of_psd_det_zero (A : Sym2)
    (hA : PositiveSemidefinite A) (hdet : A.det = 0) :
    ∃ v : Vec2, A = outer v := by
  have ha : 0 ≤ A 0 0 := psd_diag_nonneg A hA 0
  have hc : 0 ≤ A 1 1 := psd_diag_nonneg A hA 1
  rcases eq_or_lt_of_le ha with hzero | hpos
  · have h00 : A 0 0 = 0 := hzero.symm
    obtain ⟨h01, h10⟩ := psd_zero_00_offdiag A hA h00
    let v : Vec2 := ![0, Real.sqrt (A 1 1)]
    refine ⟨v, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp [outer, Matrix.vecMulVec_apply, v, h00]
    · simp [outer, Matrix.vecMulVec_apply, v, h01]
    · simp [outer, Matrix.vecMulVec_apply, v, h10]
    · simpa [outer, Matrix.vecMulVec_apply, v, sq] using (Real.sq_sqrt hc).symm
  · have hs : 0 < Real.sqrt (A 0 0) := Real.sqrt_pos.2 hpos
    have hsq : Real.sqrt (A 0 0) ^ 2 = A 0 0 := Real.sq_sqrt ha
    have hcross : A 0 0 * A 1 1 = A 0 1 ^ 2 := by
      rw [Matrix.det_fin_two, hA.1 1 0] at hdet
      nlinarith [hdet]
    let v : Vec2 := ![Real.sqrt (A 0 0), A 0 1 / Real.sqrt (A 0 0)]
    have h00' : A 0 0 = outer v 0 0 := by
      simpa [outer, Matrix.vecMulVec_apply, v, sq] using hsq.symm
    have h01' : A 0 1 = outer v 0 1 := by
      change A 0 1 = Real.sqrt (A 0 0) * (A 0 1 / Real.sqrt (A 0 0))
      field_simp [ne_of_gt hs]
    have h10' : A 1 0 = outer v 1 0 := by
      rw [hA.1 1 0]
      change A 0 1 = (A 0 1 / Real.sqrt (A 0 0)) * Real.sqrt (A 0 0)
      field_simp [ne_of_gt hs]
    have h11' : A 1 1 = outer v 1 1 := by
      change A 1 1 = (A 0 1 / Real.sqrt (A 0 0)) *
        (A 0 1 / Real.sqrt (A 0 0))
      field_simp [ne_of_gt hs]
      nlinarith [hsq, hcross]
    refine ⟨v, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h00'
    · simpa using h01'
    · simpa using h10'
    · simpa using h11'

theorem outer_ne_zero_of_vector_ne_zero {v : Vec2}
    (houter : outer v ≠ 0) : v ≠ 0 := by
  intro hv
  apply houter
  subst v
  simp [outer]

theorem row_factor_ne_zero_of_positive_entry {p q : ℕ}
    {M : Matrix (Fin p) (Fin q) ℝ}
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (hfact : Factorization M A B)
    {i : Fin p} {j : Fin q} (hpos : 0 < M i j) : A i ≠ 0 := by
  intro hzero
  have hz : M i j = 0 := by rw [hfact.2.2 i j, hzero]; simp
  linarith

theorem column_factor_ne_zero_of_positive_entry {p q : ℕ}
    {M : Matrix (Fin p) (Fin q) ℝ}
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (hfact : Factorization M A B)
    {i : Fin p} {j : Fin q} (hpos : 0 < M i j) : B j ≠ 0 := by
  intro hzero
  have hz : M i j = 0 := by rw [hfact.2.2 i j, hzero]; simp
  linarith

/-- Distinct singular row factors in a positive factorization have independent
outer-product generators. -/
theorem row_singular_pair_independent_of_distinct_rays {p q : ℕ}
    {M : Matrix (Fin p) (Fin q) ℝ}
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (hfact : Factorization M A B)
    (hdistinct : ∀ i k, SamePositiveRay (A i) (A k) → i = k)
    {i k : Fin p} (hik : i ≠ k) (j : Fin q)
    (hposi : 0 < M i j) (hposk : 0 < M k j)
    (hsingi : (A i).det = 0) (hsingk : (A k).det = 0) :
    ∃ v w : Vec2, A i = outer v ∧ A k = outer w ∧
      LinearIndependent ℝ (fun t : Fin 2 => if t = 0 then v else w) := by
  obtain ⟨v, hv⟩ := outer_of_psd_det_zero (A i) (hfact.1 i) hsingi
  obtain ⟨w, hw⟩ := outer_of_psd_det_zero (A k) (hfact.1 k) hsingk
  have hvi : v ≠ 0 := outer_ne_zero_of_vector_ne_zero
    (hv ▸ row_factor_ne_zero_of_positive_entry hfact hposi)
  have hwk : w ≠ 0 := outer_ne_zero_of_vector_ne_zero
    (hw ▸ row_factor_ne_zero_of_positive_entry hfact hposk)
  have hnotray : ¬ SamePositiveRay (outer v) (outer w) := by
    intro hray
    exact hik (hdistinct i k (hv.symm ▸ hw.symm ▸ hray))
  exact ⟨v, w, hv, hw,
    linearIndependent_of_outer_distinct hvi hwk hnotray⟩

/-- The column analogue of the singular row independence bridge. -/
theorem column_singular_pair_independent_of_distinct_rays {p q : ℕ}
    {M : Matrix (Fin p) (Fin q) ℝ}
    {A : Fin p → Sym2} {B : Fin q → Sym2}
    (hfact : Factorization M A B)
    (hdistinct : ∀ j k, SamePositiveRay (B j) (B k) → j = k)
    {j k : Fin q} (hjk : j ≠ k) (i : Fin p)
    (hposj : 0 < M i j) (hposk : 0 < M i k)
    (hsingj : (B j).det = 0) (hsingk : (B k).det = 0) :
    ∃ v w : Vec2, B j = outer v ∧ B k = outer w ∧
      LinearIndependent ℝ (fun t : Fin 2 => if t = 0 then v else w) := by
  obtain ⟨v, hv⟩ := outer_of_psd_det_zero (B j) (hfact.2.1 j) hsingj
  obtain ⟨w, hw⟩ := outer_of_psd_det_zero (B k) (hfact.2.1 k) hsingk
  have hvj : v ≠ 0 := outer_ne_zero_of_vector_ne_zero
    (hv ▸ column_factor_ne_zero_of_positive_entry hfact hposj)
  have hwk : w ≠ 0 := outer_ne_zero_of_vector_ne_zero
    (hw ▸ column_factor_ne_zero_of_positive_entry hfact hposk)
  have hnotray : ¬ SamePositiveRay (outer v) (outer w) := by
    intro hray
    exact hjk (hdistinct j k (hv.symm ▸ hw.symm ▸ hray))
  exact ⟨v, w, hv, hw,
    linearIndependent_of_outer_distinct hvj hwk hnotray⟩

end NLA.Proofs.PF05
