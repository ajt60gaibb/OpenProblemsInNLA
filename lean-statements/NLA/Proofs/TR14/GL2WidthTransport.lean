import NLA.Proofs.TR14.GL2HankelMode

/-!
Exact ordinary and symmetric width preservation under the audited
inverse-dual chart action. No equality of the two widths is asserted here.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open NLA.Statements.TR14
open scoped BigOperators
noncomputable section

private def tensorPairing {m n : ℕ} (H : (Fin m → Fin n) → ℂ)
    (u : Fin m → Fin n → ℂ) : ℂ :=
  ∑ i : Fin m → Fin n, H i * ∏ k : Fin m, u k (i k)

private theorem tensorPairing_single {m n : ℕ}
    (H : (Fin m → Fin n) → ℂ) (i : Fin m → Fin n) :
    tensorPairing H (fun k => Pi.single (i k) 1) = H i := by
  classical
  let e : Fin m → Fin n → ℂ := fun k => Pi.single (i k) 1
  change tensorPairing H e = H i
  unfold tensorPairing
  rw [Finset.sum_eq_single i]
  · simp [e]
  · intro j _ hji
    have hnot : ¬ ∀ k : Fin m, j k = i k := by
      intro h
      exact hji (funext h)
    simp only [not_forall] at hnot
    obtain ⟨k, hk⟩ := hnot
    have hz : (∏ a : Fin m, e a (j a)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      simp [e, hk]
    simp [hz]
  · simp

private theorem tensorPairing_rankOne {m n : ℕ}
    (v u : Fin m → Fin n → ℂ) :
    (∑ i : Fin m → Fin n,
      (∏ k : Fin m, v k (i k)) * ∏ k : Fin m, u k (i k)) =
      ∏ k : Fin m, ∑ j : Fin n, v k j * u k j := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (Finset.prod_mul_distrib).symm

private theorem tensorPairing_ordinaryWidth {m n r : ℕ}
    {H : (Fin m → Fin n) → ℂ} (v : Fin r → Fin m → Fin n → ℂ)
    (hv : ∀ i, H i = ∑ l : Fin r, ∏ k : Fin m, v l k (i k))
    (u : Fin m → Fin n → ℂ) :
    tensorPairing H u =
      ∑ l : Fin r, ∏ k : Fin m, ∑ j : Fin n, v l k j * u k j := by
  unfold tensorPairing
  simp_rw [hv, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  exact tensorPairing_rankOne (v l) u

private theorem tensorPairing_symmetricWidth {m n r : ℕ}
    {H : (Fin m → Fin n) → ℂ} (c : Fin r → ℂ) (v : Fin r → Fin n → ℂ)
    (hv : ∀ i, H i = ∑ l : Fin r, c l * ∏ k : Fin m, v l (i k))
    (u : Fin m → Fin n → ℂ) :
    tensorPairing H u =
      ∑ l : Fin r, c l * ∏ k : Fin m,
        ∑ j : Fin n, v l j * u k j := by
  unfold tensorPairing
  simp_rw [hv, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  calc
    (∑ i : Fin m → Fin n,
        (c l * ∏ k : Fin m, v l (i k)) * ∏ k : Fin m, u k (i k)) =
      c l * ∑ i : Fin m → Fin n,
        (∏ k : Fin m, v l (i k)) * ∏ k : Fin m, u k (i k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = _ := by rw [tensorPairing_rankOne]

/-- A coefficient vector used as a tensor factor transforms by the ordinary
inverse transpose: evaluation against the inverse image of each basis vector.
No complex conjugation is present. -/
def chartFactor (z : ℂ) (q : ℕ) (v : Fin (q + 1) → ℂ) :
    Fin (q + 1) → ℂ :=
  fun i => ∑ j : Fin (q + 1),
    v j * (chartCoefficientEquiv z q).symm (Pi.single i 1) j

/-- The reverse factor map is the ordinary transpose of the forward
coefficient chart. -/
def chartFactorBack (z : ℂ) (q : ℕ) (v : Fin (q + 1) → ℂ) :
    Fin (q + 1) → ℂ :=
  fun i => ∑ j : Fin (q + 1),
    v j * chartCoefficientEquiv z q (Pi.single i 1) j

/-- The chart preserves every ordinary width, including `r=0`. -/
theorem chart_ordinaryWidth_forward (z : ℂ) (m q r : ℕ)
    (h : Fin (m * q + 1) → ℂ)
    (hW : OrdinaryWidth (Hankel (m := m) (n := q + 1) h) r) :
    OrdinaryWidth (Hankel (m := m) (n := q + 1) (transformedMoments z h)) r := by
  obtain ⟨v, hv⟩ := hW
  refine ⟨fun l k => chartFactor z q (v l k), ?_⟩
  intro i
  let u : Fin m → Fin (q + 1) → ℂ :=
    fun k => (chartCoefficientEquiv z q).symm (Pi.single (i k) 1)
  have hPair := chart_hankel_multilinear z m q h u
  have hEntry : Hankel (m := m) (n := q + 1) (transformedMoments z h) i =
      tensorPairing (Hankel (m := m) (n := q + 1) h) u := by
    change tensorPairing (Hankel (m := m) (n := q + 1) (transformedMoments z h))
      (fun k => chartCoefficientEquiv z q (u k)) =
      tensorPairing (Hankel (m := m) (n := q + 1) h) u at hPair
    have hu : (fun k => chartCoefficientEquiv z q (u k)) =
        (fun k => Pi.single (i k) 1) := by
      funext k
      exact (chartCoefficientEquiv z q).apply_symm_apply _
    rw [hu, tensorPairing_single] at hPair
    exact hPair
  rw [hEntry]
  rw [tensorPairing_ordinaryWidth v hv u]
  rfl

/-- The chart preserves every symmetric width, with one factor map shared by
all `m` modes and the scalar coefficient unchanged. -/
theorem chart_symmetricWidth_forward (z : ℂ) (m q r : ℕ)
    (h : Fin (m * q + 1) → ℂ)
    (hW : SymmetricWidth (Hankel (m := m) (n := q + 1) h) r) :
    SymmetricWidth (Hankel (m := m) (n := q + 1) (transformedMoments z h)) r := by
  obtain ⟨c, v, hv⟩ := hW
  refine ⟨c, fun l => chartFactor z q (v l), ?_⟩
  intro i
  let u : Fin m → Fin (q + 1) → ℂ :=
    fun k => (chartCoefficientEquiv z q).symm (Pi.single (i k) 1)
  have hPair := chart_hankel_multilinear z m q h u
  have hEntry : Hankel (m := m) (n := q + 1) (transformedMoments z h) i =
      tensorPairing (Hankel (m := m) (n := q + 1) h) u := by
    change tensorPairing (Hankel (m := m) (n := q + 1) (transformedMoments z h))
      (fun k => chartCoefficientEquiv z q (u k)) =
      tensorPairing (Hankel (m := m) (n := q + 1) h) u at hPair
    have hu : (fun k => chartCoefficientEquiv z q (u k)) =
        (fun k => Pi.single (i k) 1) := by
      funext k
      exact (chartCoefficientEquiv z q).apply_symm_apply _
    rw [hu, tensorPairing_single] at hPair
    exact hPair
  rw [hEntry]
  rw [tensorPairing_symmetricWidth c v hv u]
  rfl

/-- Reverse ordinary-width transport, using the forward coefficient chart
on the test vectors. -/
theorem chart_ordinaryWidth_reverse (z : ℂ) (m q r : ℕ)
    (h : Fin (m * q + 1) → ℂ)
    (hW : OrdinaryWidth
      (Hankel (m := m) (n := q + 1) (transformedMoments z h)) r) :
    OrdinaryWidth (Hankel (m := m) (n := q + 1) h) r := by
  obtain ⟨v, hv⟩ := hW
  refine ⟨fun l k => chartFactorBack z q (v l k), ?_⟩
  intro i
  let u : Fin m → Fin (q + 1) → ℂ := fun k => Pi.single (i k) 1
  have hPair := chart_hankel_multilinear z m q h u
  have hEntry : Hankel (m := m) (n := q + 1) h i =
      tensorPairing
        (Hankel (m := m) (n := q + 1) (transformedMoments z h))
        (fun k => chartCoefficientEquiv z q (u k)) := by
    change tensorPairing
      (Hankel (m := m) (n := q + 1) (transformedMoments z h))
      (fun k => chartCoefficientEquiv z q (u k)) =
      tensorPairing (Hankel (m := m) (n := q + 1) h) u at hPair
    rw [show u = (fun k => Pi.single (i k) 1) from rfl,
      tensorPairing_single] at hPair
    exact hPair.symm
  rw [hEntry]
  rw [tensorPairing_ordinaryWidth v hv]
  rfl

/-- Reverse symmetric-width transport uses one common factor in every
mode, preserving the scalar coefficient of each summand. -/
theorem chart_symmetricWidth_reverse (z : ℂ) (m q r : ℕ)
    (h : Fin (m * q + 1) → ℂ)
    (hW : SymmetricWidth
      (Hankel (m := m) (n := q + 1) (transformedMoments z h)) r) :
    SymmetricWidth (Hankel (m := m) (n := q + 1) h) r := by
  obtain ⟨c, v, hv⟩ := hW
  refine ⟨c, fun l => chartFactorBack z q (v l), ?_⟩
  intro i
  let u : Fin m → Fin (q + 1) → ℂ := fun k => Pi.single (i k) 1
  have hPair := chart_hankel_multilinear z m q h u
  have hEntry : Hankel (m := m) (n := q + 1) h i =
      tensorPairing
        (Hankel (m := m) (n := q + 1) (transformedMoments z h))
        (fun k => chartCoefficientEquiv z q (u k)) := by
    change tensorPairing
      (Hankel (m := m) (n := q + 1) (transformedMoments z h))
      (fun k => chartCoefficientEquiv z q (u k)) =
      tensorPairing (Hankel (m := m) (n := q + 1) h) u at hPair
    rw [show u = (fun k => Pi.single (i k) 1) from rfl,
      tensorPairing_single] at hPair
    exact hPair.symm
  rw [hEntry]
  rw [tensorPairing_symmetricWidth c v hv]
  rfl

/-- Both frozen width predicates are invariant under the invertible chart,
for every `r`, including the empty decomposition. -/
theorem chart_widths_iff (z : ℂ) (m q r : ℕ)
    (h : Fin (m * q + 1) → ℂ) :
    (OrdinaryWidth (Hankel (m := m) (n := q + 1) h) r ↔
      OrdinaryWidth
        (Hankel (m := m) (n := q + 1) (transformedMoments z h)) r) ∧
    (SymmetricWidth (Hankel (m := m) (n := q + 1) h) r ↔
      SymmetricWidth
        (Hankel (m := m) (n := q + 1) (transformedMoments z h)) r) := by
  exact ⟨⟨chart_ordinaryWidth_forward z m q r h,
    chart_ordinaryWidth_reverse z m q r h⟩,
    ⟨chart_symmetricWidth_forward z m q r h,
      chart_symmetricWidth_reverse z m q r h⟩⟩

#assert_trust kernel chartFactor
#assert_trust kernel chartFactorBack
#assert_trust kernel chart_ordinaryWidth_forward
#assert_trust kernel chart_symmetricWidth_forward
#assert_trust kernel chart_ordinaryWidth_reverse
#assert_trust kernel chart_symmetricWidth_reverse
#assert_trust kernel chart_widths_iff
#print axioms chart_widths_iff

end
end NLA.Proofs.TR14
