import NLA.TR13.Definitions
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Instances.Matrix

/-!
Determinant certificates for matrix rank. Fixed changes of basis at one witness
produce a polynomial nonvanishing condition, without assuming a rank-minor
equivalence or genericity theorem.
-/

noncomputable section
open scoped BigOperators
open Filter Matrix

namespace NLA.TR13

theorem matrix_rank_add_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A B : Matrix ι κ ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact le_trans (Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin))
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem matrix_rank_finsetSum_le {α ι κ : Type*} [Fintype ι] [Fintype κ]
    (s : Finset α) (A : α → Matrix ι κ ℂ) :
    (∑ i ∈ s, A i).rank ≤ ∑ i ∈ s, (A i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (matrix_rank_add_le _ _).trans (Nat.add_le_add_left ih _)

theorem matrix_rank_sum_le {α ι κ : Type*} [Fintype α] [Fintype ι] [Fintype κ]
    (A : α → Matrix ι κ ℂ) :
    (∑ i, A i).rank ≤ ∑ i, (A i).rank :=
  matrix_rank_finsetSum_le Finset.univ A

/-- If selected coordinates determine every kernel vector, their number bounds
the nullity, giving a complementary lower bound on matrix rank. -/
theorem matrix_rank_ge_sub_of_kernel_coordinates
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (g : κ → ι)
    (hdetermine : ∀ x : ι → ℂ, A *ᵥ x = 0 → (∀ i, x (g i) = 0) → x = 0) :
    Fintype.card ι - Fintype.card κ ≤ A.rank := by
  let φ : LinearMap.ker A.mulVecLin →ₗ[ℂ] (κ → ℂ) :=
    { toFun := fun x i => x.val (g i)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hinj : Function.Injective φ := by
    apply (injective_iff_map_eq_zero φ).mpr
    intro x hx
    apply Subtype.ext
    exact hdetermine x.val (LinearMap.mem_ker.mp x.property) (fun i => congrFun hx i)
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  have hnull := A.mulVecLin.finrank_range_add_finrank_ker
  simp only [Module.finrank_fintype_fun_eq_card] at hdim hnull
  change Fintype.card ι - Fintype.card κ ≤
    Module.finrank ℂ (LinearMap.range A.mulVecLin)
  omega

/-- A fixed pair of changes of basis yields a nonzero square minor of any
prescribed size below the rank. The same minor always bounds the input rank. -/
theorem exists_fixed_rank_minor {ι : Type*} [Fintype ι] {r : ℕ} (M : Matrix ι ι ℂ)
    (hr : r ≤ M.rank) :
    ∃ (V U : Matrix ι ι ℂ) (f : Fin r → ι),
      ((V * M * U).submatrix f f).det ≠ 0 ∧
      ∀ A : Matrix ι ι ℂ,
        ((V * A * U).submatrix f f).det ≠ 0 → r ≤ A.rank := by
  classical
  obtain ⟨V, U, e, _, _, he⟩ := Matrix.exists_rank_normal_form M
  let f : Fin r → ι := fun i => e.symm (Sum.inl (Fin.castLE hr i))
  have hminor : (V * M * U).submatrix f f = 1 := by
    rw [he]
    ext i j
    simp [f, Matrix.submatrix_apply, Matrix.one_apply, Fin.castLE_inj]
  refine ⟨V, U, f, ?_, ?_⟩
  · rw [hminor, Matrix.det_one]
    exact one_ne_zero
  · intro A ha
    have hfull := Matrix.rank_of_det_ne_zero ha
    have hsub := Matrix.rank_submatrix_le (V * A * U) f f
    have hmul := (Matrix.rank_mul_le_left (V * A) U).trans
      (Matrix.rank_mul_le_right V A)
    simpa only [hfull, Fintype.card_fin] using hsub.trans hmul

/-- Matrix rank cannot jump upward in a limit of matrices of bounded rank.
The argument uses a single continuous determinant after fixed changes of
basis, so it imposes no boundedness assumptions on matrix factorizations. -/
theorem matrix_rank_le_of_tendsto {ι : Type*} [Fintype ι] {q : ℕ}
    (A : ℕ → Matrix ι ι ℂ) (M : Matrix ι ι ℂ)
    (hlim : Tendsto A atTop (nhds M)) (hr : ∀ k, (A k).rank ≤ q) :
    M.rank ≤ q := by
  by_contra hnot
  have hlarge : q + 1 ≤ M.rank := by omega
  obtain ⟨V, U, f, hw, hbound⟩ := exists_fixed_rank_minor M hlarge
  let D : Matrix ι ι ℂ → ℂ :=
    fun B => ((V * B * U).submatrix f f).det
  have hcont : Continuous D := by fun_prop
  have hzero (k : ℕ) : D (A k) = 0 := by
    by_contra hz
    have := hbound (A k) hz
    have := hr k
    omega
  have hDlim : Tendsto (fun k => D (A k)) atTop (nhds (D M)) :=
    hcont.continuousAt.tendsto.comp hlim
  have hconst : (fun k => D (A k)) = fun _ => 0 := funext hzero
  rw [hconst] at hDlim
  exact hw (tendsto_nhds_unique hDlim tendsto_const_nhds)

/-- A polynomial matrix with a witness of rank at least `r` admits a single
nonzero determinant polynomial whose nonvanishing certifies rank at least `r`.
Its value at the original witness is nonzero as well. -/
theorem exists_polynomial_rank_certificate {σ ι : Type*} [Fintype ι] {r : ℕ}
    (Kp : Matrix ι ι (MvPolynomial σ ℂ))
    (h0 : σ → ℂ) (hr : r ≤ (Kp.map (MvPolynomial.eval h0)).rank) :
    ∃ p : MvPolynomial σ ℂ, p ≠ 0 ∧ MvPolynomial.eval h0 p ≠ 0 ∧
      ∀ h : σ → ℂ,
        MvPolynomial.eval h p ≠ 0 → r ≤ (Kp.map (MvPolynomial.eval h)).rank := by
  obtain ⟨V, U, f, hw, hbound⟩ := exists_fixed_rank_minor
    (Kp.map (MvPolynomial.eval h0)) hr
  let P := ((V.map MvPolynomial.C * Kp * U.map MvPolynomial.C).submatrix f f).det
  have heval (h : σ → ℂ) : MvPolynomial.eval h P =
      ((V * Kp.map (MvPolynomial.eval h) * U).submatrix f f).det := by
    simp [P, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul,
      ← Matrix.submatrix_map, Matrix.map_map, Function.comp_def]
  have hp : MvPolynomial.eval h0 P ≠ 0 := by rwa [heval]
  refine ⟨P, ?_, hp, ?_⟩
  · intro hz
    exact hp (by rw [hz, map_zero])
  · intro h hh
    exact hbound _ (by rwa [← heval])

end NLA.TR13
