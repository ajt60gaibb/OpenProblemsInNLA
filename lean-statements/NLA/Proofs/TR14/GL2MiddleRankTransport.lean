import NLA.Proofs.TR14.GL2ChartNormalize
import NLA.Proofs.TR14.MiddleCatalecticant

/-!
Rank of the exact middle Hankel catalecticant is invariant under the genuine
inverse-dual chart. The proof uses its exact degree-`ceil(D/2)` apolar kernel
and rank-nullity, avoiding determinant expansion. This module asserts no
ordinary/symmetric tensor-width equality or frozen Target.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open scoped BigOperators
noncomputable section

private theorem middle_split (D : ℕ) :
    D - (D + 1) / 2 = D / 2 := by omega

private theorem middle_right_le (D : ℕ) : (D + 1) / 2 ≤ D := by omega

/-- The rectangular middle matrix acts on degree-`ceil(D/2)` coefficients
by the exact apolar convolution, with all rows from zero to `floor(D/2)`.
There is no truncation at odd or even `D`, including `D=0`. -/
theorem middleCatalecticant_mulVec_eq_apolar {D : ℕ}
    (h : Fin (D + 1) → ℂ)
    (g : Fin ((D + 1) / 2 + 1) → ℂ)
    (i : Fin (D / 2 + 1)) :
    (middleCatalecticant h).mulVecLin g i =
      (apolarMap h ((D + 1) / 2) (middle_right_le D) g)
        (Fin.cast (congrArg (· + 1) (middle_split D)).symm i) := by
  change (∑ j : Fin ((D + 1) / 2 + 1),
      h ⟨i.val + j.val, by have hi := i.isLt; have hj := j.isLt; omega⟩ * g j) =
    ∑ j : Fin ((D + 1) / 2 + 1),
      g j * h ⟨j.val + (Fin.cast (congrArg (· + 1) (middle_split D)).symm i).val,
        by have hi := i.isLt; have hj := j.isLt; omega⟩
  apply Finset.sum_congr rfl
  intro j hj
  have hidx : (⟨i.val + j.val, by have hi := i.isLt; have hj := j.isLt; omega⟩ :
      Fin (D + 1)) =
      ⟨j.val + (Fin.cast (congrArg (· + 1) (middle_split D)).symm i).val,
        by have hi := i.isLt; have hj := j.isLt; omega⟩ := by
    apply Fin.ext
    simp [Nat.add_comm]
  rw [hidx]
  ring

/-- The middle matrix kernel is exactly the full degree-`ceil(D/2)`
apolar kernel, as submodules of the same coefficient-vector space. -/
theorem middleCatalecticant_ker_eq_apolar {D : ℕ}
    (h : Fin (D + 1) → ℂ) :
    LinearMap.ker (middleCatalecticant h).mulVecLin =
      LinearMap.ker (apolarMap h ((D + 1) / 2) (middle_right_le D)) := by
  ext g
  simp only [LinearMap.mem_ker]
  constructor
  · intro hg
    funext j
    let i : Fin (D / 2 + 1) :=
      Fin.cast (congrArg (· + 1) (middle_split D)) j
    have hi := congrFun hg i
    rw [middleCatalecticant_mulVec_eq_apolar] at hi
    simpa [i] using hi
  · intro hg
    funext i
    rw [middleCatalecticant_mulVec_eq_apolar]
    exact congrFun hg _

/-- Every degree-`b` apolar kernel maps under the already audited invertible
coefficient chart to the transformed degree-`b` kernel. -/
private def middleKernelEquiv (z : ℂ) {D : ℕ}
    (h : Fin (D + 1) → ℂ) :
    ↥(LinearMap.ker (middleCatalecticant h).mulVecLin) ≃ₗ[ℂ]
      ↥(LinearMap.ker (middleCatalecticant (transformedMoments z h)).mulVecLin) := by
  let b := (D + 1) / 2
  let A := chartCoefficientEquiv z b
  have hmem (g : Fin (b + 1) → ℂ) :
      g ∈ LinearMap.ker (middleCatalecticant h).mulVecLin ↔
        A g ∈ LinearMap.ker
          (middleCatalecticant (transformedMoments z h)).mulVecLin := by
    rw [middleCatalecticant_ker_eq_apolar,
      middleCatalecticant_ker_eq_apolar]
    change IsApolar h b (middle_right_le D) g ↔
      IsApolar (transformedMoments z h) b (middle_right_le D) (A g)
    exact apolar_iff_chart_apolar z (middle_right_le D) h g
  exact {
    toFun := fun g => ⟨A g.1, (hmem g.1).mp g.2⟩
    invFun := fun g => ⟨A.symm g.1, by
      apply (hmem (A.symm g.1)).mpr
      simpa only [A.apply_symm_apply] using g.2⟩
    left_inv := fun g => by apply Subtype.ext; exact A.symm_apply_apply g.1
    right_inv := fun g => by apply Subtype.ext; exact A.apply_symm_apply g.1
    map_add' := fun x y => by apply Subtype.ext; exact A.map_add x.1 y.1
    map_smul' := fun c x => by apply Subtype.ext; exact A.map_smul c x.1
  }

/-- Original and inverse-dual-chart middle catalecticants have exactly the
same rank for every moment vector and every degree, including zero. -/
theorem middleCatalecticant_rank_chart (z : ℂ) {D : ℕ}
    (h : Fin (D + 1) → ℂ) :
    (middleCatalecticant (transformedMoments z h)).rank =
      (middleCatalecticant h).rank := by
  let C := middleCatalecticant h
  let C' := middleCatalecticant (transformedMoments z h)
  have hker : Module.finrank ℂ (LinearMap.ker C.mulVecLin) =
      Module.finrank ℂ (LinearMap.ker C'.mulVecLin) :=
    (middleKernelEquiv z h).finrank_eq
  have hnull := C.mulVecLin.finrank_range_add_finrank_ker
  have hnull' := C'.mulVecLin.finrank_range_add_finrank_ker
  change C'.rank = C.rank
  rw [Matrix.rank, Matrix.rank]
  omega

/-- The normalized middle-rank theorem now holds in the original coordinates
for any selected nonzero least apolar form, even when that form has a root at
infinity or the balanced least kernel has more than one generator. -/
theorem middleCatalecticant_rank_minimal {D r₀ : ℕ}
    (h : Fin (D + 1) → ℂ) (hD : 1 ≤ D) (hh : h ≠ 0)
    (hrD : r₀ ≤ D) (hrLo : 1 ≤ r₀) (hrHi : r₀ ≤ D / 2 + 1)
    (g : Fin (r₀ + 1) → ℂ) (hg : g ≠ 0)
    (hAp : IsApolar h r₀ hrD g)
    (hmin : ∀ k : ℕ, ∀ hk : k ≤ D, k < r₀ →
      ∀ c : Fin (k + 1) → ℂ, IsApolar h k hk c → c = 0) :
    (middleCatalecticant h).rank = r₀ := by
  obtain ⟨z, b, q, hh', _hb, hApB, _hbTop,
    hqMonic, hqDegree, hqCoeff, hmin'⟩ :=
    normalize_chosen_minimal_apolar h hD hh hrD hrLo hrHi g hg hAp hmin
  subst r₀
  have hcoeff : (fun i : Fin (q.natDegree + 1) => q.coeff i.val) = b :=
    funext hqCoeff
  have hApQ : IsApolar (transformedMoments z h) q.natDegree
      hrD
      (fun i : Fin (q.natDegree + 1) => q.coeff i.val) := by
    simpa only [hcoeff] using hApB
  have hminQ : ∀ k : ℕ, ∀ hk : k ≤ D, k < q.natDegree →
      ∀ c : Fin (k + 1) → ℂ,
        IsApolar (transformedMoments z h) k hk c → c = 0 := by
    intro k hk hlt c hc
    exact hmin' k hk (by omega) c hc
  have hrank := middleCatalecticant_rank_normalized
    (transformedMoments z h) hh' q hqMonic
      (by omega) (by omega) (by omega) hApQ hminQ
  exact (middleCatalecticant_rank_chart z h).symm.trans hrank

#assert_trust kernel middleCatalecticant_mulVec_eq_apolar
#assert_trust kernel middleCatalecticant_ker_eq_apolar
#assert_trust kernel middleKernelEquiv
#assert_trust kernel middleCatalecticant_rank_chart
#assert_trust kernel middleCatalecticant_rank_minimal
#print axioms middleCatalecticant_rank_chart
#print axioms middleCatalecticant_rank_minimal

end
end NLA.Proofs.TR14
