import NLA.Proofs.TR14.CyclicSpanDimension
import NLA.Proofs.TR14.NormalizedQuotient

/-! Exact dimensions of actual quotient polynomial images in multiplication
blocks. The cyclic orbit proof applies to every actual multiplier, so in
particular to each primitive idempotent's moment-algebra component. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open Polynomial
open scoped BigOperators Polynomial
noncomputable section

/-- The actual image subspace of polynomials with n coefficients after
multiplication by the given quotient element. -/
def blockPolynomialImage (g : ℂ[X]) (e : AdjoinRoot g) (n : ℕ) :
    Submodule ℂ (AdjoinRoot g) :=
  Submodule.span ℂ (Set.range (fun k : Fin n => e * (AdjoinRoot.root g) ^ k.val))

/-- The whole actual multiplication block, with no assumed rank invariant. -/
def blockIdeal (g : ℂ[X]) (e : AdjoinRoot g) : Submodule ℂ (AdjoinRoot g) :=
  LinearMap.range (LinearMap.mulLeft ℂ e)

/-- The actual finite coefficient-to-block map. -/
def blockModeLinear (g : ℂ[X]) (e : AdjoinRoot g) (n : ℕ) :
    (Fin n → ℂ) →ₗ[ℂ] AdjoinRoot g where
  toFun p := ∑ k, p k • (e * (AdjoinRoot.root g) ^ k.val)
  map_add' p q := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c p := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_smul, smul_eq_mul, Finset.smul_sum]

/-- The coordinate map has exactly the displayed span as its image. -/
theorem blockModeLinear_range (g : ℂ[X]) (e : AdjoinRoot g) (n : ℕ) :
    LinearMap.range (blockModeLinear g e n) = blockPolynomialImage g e n := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    change (∑ k, p k • (e * (AdjoinRoot.root g) ^ k.val)) ∈
      Submodule.span ℂ (Set.range fun k : Fin n => e * (AdjoinRoot.root g) ^ k.val)
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨k, rfl⟩))
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    refine ⟨Pi.single k 1, ?_⟩
    simp [blockModeLinear]

/-- Multiplication by the quotient generator gives its literal power orbit. -/
theorem block_shift_power (g : ℂ[X]) (e : AdjoinRoot g) (k : ℕ) :
    ((LinearMap.mulLeft ℂ (AdjoinRoot.root g)) ^ k) e = e * (AdjoinRoot.root g) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change AdjoinRoot.root g *
      (((LinearMap.mulLeft ℂ (AdjoinRoot.root g)) ^ k) e) = _
    rw [ih, pow_succ]
    ring

/-- The full actual cyclic orbit is precisely the multiplication image;
the quotient power basis supplies every element of that image. -/
theorem block_cyclicSpan_eq_range (g : ℂ[X]) (hg : g.Monic) (e : AdjoinRoot g) :
    cyclicSpan (LinearMap.mulLeft ℂ (AdjoinRoot.root g)) e = blockIdeal g e := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change ((LinearMap.mulLeft ℂ (AdjoinRoot.root g)) ^ k) e ∈ blockIdeal g e
    rw [block_shift_power]
    exact ⟨(AdjoinRoot.root g) ^ k, rfl⟩
  · rintro _ ⟨a, rfl⟩
    change e * a ∈ cyclicSpan (LinearMap.mulLeft ℂ (AdjoinRoot.root g)) e
    have ha := (AdjoinRoot.powerBasis' hg).basis.sum_repr a
    simp only [(AdjoinRoot.powerBasis' hg).basis_eq_pow] at ha
    change (∑ i : Fin g.natDegree,
      (((AdjoinRoot.powerBasis' hg).basis.repr a) i) • (AdjoinRoot.root g) ^ i.val) = a at ha
    rw [← ha, Finset.mul_sum]
    apply Submodule.sum_mem
    intro i _hi
    have hpow : e * (AdjoinRoot.root g) ^ i.val ∈
        cyclicSpan (LinearMap.mulLeft ℂ (AdjoinRoot.root g)) e := by
      rw [← block_shift_power]
      exact Submodule.subset_span ⟨i.val, rfl⟩
    simpa only [mul_smul_comm] using
      (cyclicSpan (LinearMap.mulLeft ℂ (AdjoinRoot.root g)) e).smul_mem
        (((AdjoinRoot.powerBasis' hg).basis.repr a) i) hpow

/-- The actual block polynomial image has dimension min(n,ρ), where ρ is
the actual dimension of the multiplication block. Idempotence is unnecessary. -/
theorem blockPolynomialImage_finrank (g : ℂ[X]) (hg : g.Monic)
    (e : AdjoinRoot g) (n : ℕ) :
    Module.finrank ℂ (blockPolynomialImage g e n) =
      min n (Module.finrank ℂ (blockIdeal g e)) := by
  let : Module.Finite ℂ (AdjoinRoot g) := hg.finite_adjoinRoot
  have hdim := cyclicPrefix_finrank (LinearMap.mulLeft ℂ (AdjoinRoot.root g)) e n
  rw [block_cyclicSpan_eq_range g hg e] at hdim
  have hpref : cyclicPrefix (LinearMap.mulLeft ℂ (AdjoinRoot.root g)) e n =
      blockPolynomialImage g e n := by
    change Submodule.span ℂ (Set.range fun k : Fin n =>
      ((LinearMap.mulLeft ℂ (AdjoinRoot.root g)) ^ k.val) e) =
      Submodule.span ℂ (Set.range fun k : Fin n => e * (AdjoinRoot.root g) ^ k.val)
    apply congrArg (Submodule.span ℂ)
    apply congrArg Set.range
    funext k
    exact block_shift_power g e k.val
  rw [hpref] at hdim
  exact hdim

/-- The same exact rank formula for the actual finite coordinate map. -/
theorem blockModeLinear_finrank_range (g : ℂ[X]) (hg : g.Monic)
    (e : AdjoinRoot g) (n : ℕ) :
    Module.finrank ℂ (LinearMap.range (blockModeLinear g e n)) =
      min n (Module.finrank ℂ (blockIdeal g e)) := by
  rw [blockModeLinear_range]
  exact blockPolynomialImage_finrank g hg e n

#assert_trust kernel blockModeLinear_range
#assert_trust kernel block_cyclicSpan_eq_range
#assert_trust kernel blockPolynomialImage_finrank
#assert_trust kernel blockModeLinear_finrank_range
#print axioms blockModeLinear_finrank_range

end
end NLA.Proofs.TR14
