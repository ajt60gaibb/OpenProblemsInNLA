import NLA.Proofs.PF05.ActualContactChart
import NLA.Proofs.PF05.StrictPSD

/-! Direct positive-case obstruction: a nonzero actual alternative quartic
produces an actual nonscalar feasible straight direction. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05
open NLA.Statements.PF05 CoordinateActions Polynomial
noncomputable section

/-- An actual alternative has the weak determinant signs at all actual
singular contacts. Its inverse-dual identity is derived from rank three. -/
theorem alternativePolynomial_contact_weak {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A At : Fin p → M2) (B Bt : Fin q → M2)
    (hf : Factorization M A B) (hft : Factorization M At Bt) (hrank : M.rank=3)
    (ha : ∀ i, 0 < A i 0 0) (hb : ∀ j, 0 < B j 1 1)
    (L : M3) (hAt : ∀ i, At i=primal L (A i)) :
    ∀ i : ContactIndex A B,
      0 ≤ contactSign A B i * (alternativePolynomial L).eval (contactNode A B i) := by
  have hdual := actual_dual_identity_of_primal M A At B Bt hf hft hrank L hAt
  intro i
  cases i with
  | inl i =>
    have hc := singular_primal_chart (A i) (hf.1 i).1 (ha i) i.property
    have hdet := psd_det_nonneg (At i) (hft.1 i)
    have he : (At i).det = (A i 0 0)^2 *
        (alternativePolynomial L).eval (primalSlope (A i)) := by
      conv_lhs => rw [hAt i, hc, primal_smul_input, Matrix.det_smul]
      simp [← alternativePolynomial_eval]
    rw [he] at hdet
    have hn := nonneg_of_mul_nonneg_right hdet (sq_pos_of_pos (ha i))
    simpa [contactSign, contactNode] using hn
  | inr j =>
    have hc := singular_dual_chart (B j) (hf.2.1 j).1 (hb j) j.property
    have hne : Bt j ≠ 0 := by
      intro hz
      have he := congrArg (fun C : M2 => C 1 1) (hdual j)
      rw [hz, dual_zero_input] at he
      have hp := hb j
      simp at he
      linarith
    have htr : Matrix.trace (primal L (chartOuter (dualSlope (B j))) * Bt j)=0 := by
      rw [coordinateActions_trace_pairing L _ _ (by
        intro a b; fin_cases a <;> fin_cases b <;> rfl) (hft.2.1 j).1,
        hdual j]
      have hh := congrArg (fun C : M2 => Matrix.trace (chartOuter (dualSlope (B j))*C)) hc
      rw [Matrix.mul_smul, Matrix.trace_smul, chart_trace_same] at hh
      simpa using hh
    have hn := det_nonpos_of_trace_zero_psd _ _ (primal_symmetric _ _)
      (hft.2.1 j) hne htr
    rw [← alternativePolynomial_eval] at hn
    simpa [contactSign, contactNode] using neg_nonneg.mpr hn

/-- Strict finite contact signs of an actual quartic yield an actual feasible
coordinate direction for the complete two families, including definite factors. -/
theorem quartic_strict_actions_feasible {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → M2) (B : Fin q → M2)
    (hf : Factorization M A B) (ha : ∀ i, 0 < A i 0 0) (hb : ∀ j, 0 < B j 1 1)
    (r : ℝ[X]) (hr : r.natDegree ≤ 4)
    (hstrict : ∀ i : ContactIndex A B, 0 < contactSign A B i * r.eval (contactNode A B i)) :
    FeasibleDirection A (fun i => primal (quarticAction r) (A i))
      B (fun j => -dual (quarticAction r) (B j)) := by
  have hpoly := directionPolynomial_quarticAction r hr
  apply strict_actions_feasible M A B hf
  · intro i hz
    have he := congrArg (fun C : M2 => C 0 0) hz
    have hp := ha i
    simp at he
    linarith
  · intro j hz
    have he := congrArg (fun C : M2 => C 1 1) hz
    have hp := hb j
    simp at he
    linarith
  · intro i hd
    have hc := singular_primal_chart (A i) (hf.1 i).1 (ha i) hd
    have he : determinantDirection (A i) (primal (quarticAction r) (A i)) =
        (A i 0 0)^2 * r.eval (primalSlope (A i)) := by
      conv_lhs => rw [hc]
      rw [primal_smul_input, determinantDirection_smul, ← directionPolynomial_eval, hpoly]
    rw [he]
    exact mul_pos (sq_pos_of_pos (ha i)) (by simpa [contactSign, contactNode] using
      (hstrict (.inl ⟨i,hd⟩)))
  · intro j hd
    have hc := singular_dual_chart (B j) (hf.2.1 j).1 (hb j) hd
    have he : determinantDirection (B j) (-dual (quarticAction r) (B j)) =
        (B j 1 1)^2 * (-r.eval (dualSlope (B j))) := by
      conv_lhs => rw [hc]
      rw [dual_smul_input, ← smul_neg, determinantDirection_smul,
        ← directionPolynomial_dual_eval, hpoly]
    rw [he]
    exact mul_pos (sq_pos_of_pos (hb j)) (by simpa [contactSign, contactNode] using
      (hstrict (.inr ⟨j,hd⟩)))

/-- Under actual frozen straight rigidity, every actual alternative preserves
the whole rank-one conic. The only finite-node assumptions here are obtained
by the retained positive-ray compression and the actual common affine chart. -/
theorem rigid_chart_alternativePolynomial_zero {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A At : Fin p → M2) (B Bt : Fin q → M2)
    (hf : Factorization M A B) (hft : Factorization M At Bt) (hrank : M.rank=3)
    (hpos : ∀ i j, 0 < M i j) (ha : ∀ i, 0 < A i 0 0) (hb : ∀ j, 0 < B j 1 1)
    (hda : ∀ i k, SamePositiveRay (A i) (A k) → i=k)
    (hdb : ∀ j k, SamePositiveRay (B j) (B k) → j=k)
    (hRigid : InfinitesimallyRigid A B) (L : M3) (hAt : ∀ i, At i=primal L (A i)) :
    alternativePolynomial L=0 := by
  classical
  by_contra hp
  let ι := ContactIndex A B
  letI : Fintype ι := by dsimp [ι, ContactIndex]; infer_instance
  have hx : Set.InjOn (contactNode A B) (Finset.univ : Finset ι) :=
    (contactNode_injective M A B hf hpos ha hb hda hdb).injOn
  obtain ⟨r, hr, hrne, hstrict⟩ := polynomial_signed_strictification
    (Finset.univ : Finset ι) (contactNode A B) (contactSign A B) hx
    (fun i _ => contactSign_ne_zero A B i) (alternativePolynomial L) hp 4
    (alternativePolynomial_degree L)
    (fun i _ => alternativePolynomial_contact_weak M A At B Bt hf hft hrank ha hb L hAt i)
  have hfeas := quartic_strict_actions_feasible M A B hf ha hb r hr
    (fun i => hstrict i (Finset.mem_univ _))
  obtain ⟨d, hd, _⟩ := hRigid _ _ hfeas
  apply hrne
  rw [← directionPolynomial_quarticAction r hr]
  exact directionPolynomial_zero_of_scalar M A B hf hrank (quarticAction r) d hd

#assert_trust kernel alternativePolynomial_contact_weak
#assert_trust kernel quartic_strict_actions_feasible
#assert_trust kernel rigid_chart_alternativePolynomial_zero
#print axioms rigid_chart_alternativePolynomial_zero
end
end NLA.Proofs.PF05
