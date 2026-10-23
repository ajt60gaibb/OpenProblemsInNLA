import NLA.Proofs.TR06.AdditionFiniteFibers

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open Set

namespace NLA.Proofs.TR06
open NLA.TR06 NLA.TR06.Proposed

variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

theorem addition_pullback_ne_zero_of_exact_rank_witness (hd : 0 < d)
    (p : MvPolynomial (TensorIndex d n) ℂ) (A : Tensor ℂ d n)
    (hArank : ExactRank r A) (hpA : MvPolynomial.eval (fun q => A q) p ≠ 0) :
    additionAlgebraHom d n r p ≠ 0 := by
  obtain ⟨a, ha⟩ := hArank.1
  have harange : a ∈ Set.range (characterTuple (d := d) (n := n) (r := r)) := by
    rw [range_characterTuple hd]
    exact fun i => Or.inr (ha.1 i)
  obtain ⟨f, hf⟩ := harange
  intro hzero
  have h := DFunLike.congr_fun (character_comp_addition f) p
  have hsum : (∑ i, characterTuple f i) = A := by rw [hf, ha.2]
  rw [AlgHom.comp_apply, hzero, map_zero, MvPolynomial.aeval_eq_eval, hsum] at h
  exact hpA h.symm

/-- A genuine polynomial good base simultaneously has complete real addition
properness and exact real rank/identifiability for every actual decomposition.
All of these are derived from the original generic-complex hypothesis. -/
theorem generic_identifiability_good_base (hd : 0 < d) (hn : ∀ j, 0 < n j)
    (hr : 2 ≤ r) (hgen : GenericComplexIdentifiable d n r) :
    ∃ q : MvPolynomial (TensorIndex d n) ℂ,
      additionAlgebraHom d n r q ≠ 0 ∧
      IsOpen {A : Tensor ℝ d n | MvPolynomial.eval (fun k => complexify A k) q ≠ 0} ∧
      IdentifiableAdditionOn (r := r)
        {A : Tensor ℝ d n | MvPolynomial.eval (fun k => complexify A k) q ≠ 0} ∧
      CompactAdditionPreimagesOn (r := r)
        {A : Tensor ℝ d n | MvPolynomial.eval (fun k => complexify A k) q ≠ 0} := by
  classical
  rcases hgen with ⟨p, ⟨A, hArank, hpA⟩, hident⟩
  obtain ⟨_hqf, t, ht, hfinite⟩ := addition_finite_localization d n r hd
    ⟨A, hArank, hident A hArank hpA⟩
  let : Module.Finite (Localization.Away t)
      (Localization (Algebra.algebraMapSubmonoid (SegreSource d n r) (Submonoid.powers t))) := hfinite
  let q := additionRepresentative t * p
  have htval : t.val ≠ 0 := by
    intro hzero
    exact ht (Subtype.ext hzero)
  have hpull : additionAlgebraHom d n r q ≠ 0 := by
    simpa only [q, map_mul, additionRepresentative_spec] using
      mul_ne_zero htval (addition_pullback_ne_zero_of_exact_rank_witness hd p A hArank hpA)
  have hU : {B : Tensor ℝ d n | MvPolynomial.eval (fun k => complexify B k) q ≠ 0} =
      realAdditionGoodSet t ∩
        {B : Tensor ℝ d n | MvPolynomial.eval (fun k => complexify B k) p ≠ 0} := by
    ext B
    simp only [q, map_mul, mul_ne_zero_iff, Set.mem_ofPred_eq, Set.mem_inter_iff,
      realAdditionGoodSet, additionBaseValue]
  have hpcont : Continuous (fun B : Tensor ℝ d n =>
      MvPolynomial.eval (fun k => complexify B k) p) :=
    (MvPolynomial.continuous_eval p).comp
      ((PiLp.continuous_ofLp 2 _).comp isClosedEmbedding_complexify.continuous)
  refine ⟨q, hpull, ?_, ?_, ?_⟩
  · rw [hU]
    exact (isOpen_realAdditionGoodSet t).inter (isOpen_ne_fun hpcont continuous_const)
  · rw [hU]
    intro B hB hdec
    have hcomplex := complex_exactRank_on_real_good_base hd hn hr t B hB.1 hdec
    exact exact_identifiable_of_complexify hdec ⟨hcomplex, hident (complexify B) hcomplex hB.2⟩
  · rw [hU]
    intro K hK hKU
    exact real_addition_preimages_compact hd t K hK (fun B hB => (hKU hB).1)

#print axioms addition_pullback_ne_zero_of_exact_rank_witness
#print axioms generic_identifiability_good_base
#assert_trust kernel addition_pullback_ne_zero_of_exact_rank_witness
#assert_trust kernel generic_identifiability_good_base

end NLA.Proofs.TR06
