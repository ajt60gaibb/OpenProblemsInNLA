import NLA.TR06.SegreCoordinates
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Ideal.Quotient.Operations
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open Set

namespace NLA.Proofs.TR06.GraphAlgebra
open NLA.TR06 NLA.TR06.Segre

variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

abbrev Variable (q₀ : Fin r → TensorIndex d n) := Sum (Coordinate q₀) (Fin r)
abbrev PolynomialRing (q₀ : Fin r → TensorIndex d n) := MvPolynomial (Variable q₀) ℂ

def summand (q₀ : Fin r → TensorIndex d n) (i : Fin r) (q : TensorIndex d n) :
    PolynomialRing q₀ := MvPolynomial.rename Sum.inl (summandPolynomial ℂ q₀ i q)

def radius (q₀ : Fin r → TensorIndex d n) (i : Fin r) : PolynomialRing q₀ :=
  MvPolynomial.X (Sum.inr i)

/-- Complex polynomial equations for the actual real positive radii. Complex
extraneous branches are retained in the ring, rather than discarded by fiat. -/
def radiusEquation (q₀ : Fin r → TensorIndex d n) (i : Fin r) : PolynomialRing q₀ :=
  radius q₀ i ^ 2 - ∑ q, summand q₀ i q ^ 2

def radiusIdeal (q₀ : Fin r → TensorIndex d n) : Ideal (PolynomialRing q₀) :=
  Ideal.span (Set.range (radiusEquation q₀))

abbrev QuotientRing (q₀ : Fin r → TensorIndex d n) := PolynomialRing q₀ ⧸ radiusIdeal q₀

def quotientHom (q₀ : Fin r → TensorIndex d n) : PolynomialRing q₀ →ₐ[ℂ] QuotientRing q₀ :=
  Ideal.Quotient.mkₐ ℂ (radiusIdeal q₀)

def denominator (q₀ : Fin r → TensorIndex d n) : QuotientRing q₀ :=
  ∏ i : Fin r, quotientHom q₀ (radius q₀ i)

/-- The genuine finite-type algebra of pivot coordinates and all radius
branches, restricted to nonzero radii. No graph-fiber bound is assumed. -/
abbrev Source (q₀ : Fin r → TensorIndex d n) := Localization.Away (denominator q₀)

def sourceHom (q₀ : Fin r → TensorIndex d n) : PolynomialRing q₀ →ₐ[ℂ] Source q₀ :=
  (IsScalarTower.toAlgHom ℂ (QuotientRing q₀) (Source q₀)).comp (quotientHom q₀)

def sourceRadius (q₀ : Fin r → TensorIndex d n) (i : Fin r) : Source q₀ :=
  sourceHom q₀ (radius q₀ i)

def sourceSummand (q₀ : Fin r → TensorIndex d n) (i : Fin r) (q : TensorIndex d n) : Source q₀ :=
  sourceHom q₀ (summand q₀ i q)

def sourceRadiusInverse (q₀ : Fin r → TensorIndex d n) (i : Fin r) : Source q₀ :=
  algebraMap (QuotientRing q₀) (Source q₀)
    (∏ j ∈ Finset.univ.erase i, quotientHom q₀ (radius q₀ j)) *
    IsLocalization.Away.invSelf (denominator q₀)

theorem sourceRadius_mul_inverse (q₀ : Fin r → TensorIndex d n) (i : Fin r) :
    sourceRadius q₀ i * sourceRadiusInverse q₀ i = 1 := by
  classical
  have hprod : sourceRadius q₀ i * algebraMap (QuotientRing q₀) (Source q₀)
      (∏ j ∈ Finset.univ.erase i, quotientHom q₀ (radius q₀ j)) =
      algebraMap (QuotientRing q₀) (Source q₀) (denominator q₀) := by
    change algebraMap (QuotientRing q₀) (Source q₀) (quotientHom q₀ (radius q₀ i)) * _ = _
    rw [← map_mul]
    congr 1
    exact Finset.mul_prod_erase Finset.univ (fun j : Fin r => quotientHom q₀ (radius q₀ j)) (Finset.mem_univ i)
  change sourceRadius q₀ i * (_ * _) = 1
  rw [← mul_assoc, hprod, IsLocalization.Away.mul_invSelf]

theorem sourceRadius_sq (q₀ : Fin r → TensorIndex d n) (i : Fin r) :
    sourceRadius q₀ i ^ 2 = ∑ q, sourceSummand q₀ i q ^ 2 := by
  have hQ : quotientHom q₀ (radiusEquation q₀ i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  have h := congrArg (algebraMap (QuotientRing q₀) (Source q₀)) hQ
  rw [map_zero] at h
  change sourceHom q₀ (radiusEquation q₀ i) = 0 at h
  simpa only [radiusEquation, map_sub, map_pow, map_sum, sourceRadius, sourceSummand,
    sub_eq_zero] using h

abbrev OutputCoordinate (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :=
  Sum (TensorIndex d n) (Fin r × TensorIndex d n)

/-- Exact input and individually normalized output coordinates in the genuine
radius algebra. -/
def graphCoordinate (q₀ : Fin r → TensorIndex d n) : OutputCoordinate d n r → Source q₀
  | Sum.inl q => ∑ i, sourceSummand q₀ i q
  | Sum.inr (i, q) => sourceSummand q₀ i q * sourceRadiusInverse q₀ i

instance source_finiteType (q₀ : Fin r → TensorIndex d n) : Algebra.FiniteType ℂ (Source q₀) := by
  infer_instance

#print axioms sourceRadius_mul_inverse
#print axioms sourceRadius_sq
#assert_trust kernel sourceRadius_mul_inverse
#assert_trust kernel sourceRadius_sq

end NLA.Proofs.TR06.GraphAlgebra
