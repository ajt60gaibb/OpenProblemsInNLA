# MI-27 C12: exact finite-mixture statements before bodies

Author: /root. No proof bodies or new definitions exist yet. Two independent
statement approvals are required before implementation. All matrix operations,
`StrictDensity`, `E`, `chi`, `relEntropy`, and scalar kernels are exactly the
already frozen MI27 definitions. This packet does not assert completed C12.

## Exact new headers

Inside namespace `NLA.MI27`, with the same complex matrix order/L2Operator
scopes as the frozen Challenge:

```lean
lemma c12_mixture_strict_density {n : ℕ} (ρ σ : Mat n)
    (hρ : StrictDensity ρ) (hσ : StrictDensity σ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    StrictDensity ((a : ℂ) • ρ + (b : ℂ) • σ)

lemma c12_chi_relative_entropy {n : ℕ} (ρ σ : Mat n) (a b : ℝ) :
    chi a b ρ σ =
      a * relEntropy ρ ((a : ℂ) • ρ + (b : ℂ) • σ) +
      b * relEntropy σ ((a : ℂ) • ρ + (b : ℂ) • σ)

lemma c12_E_mixture_forward {n : ℕ} (ρ σ : Mat n)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (a b γ : ℝ) (ha : 0 < a) (hb : 0 < b) (hγ : 1 ≤ γ) :
    E (γ / (b + a * γ)) ρ ((a : ℂ) • ρ + (b : ℂ) • σ) =
      (b / (b + a * γ)) * E γ ρ σ

lemma c12_E_mixture_reverse {n : ℕ} (ρ σ : Mat n)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (a b γ : ℝ) (hb : 0 ≤ b) :
    E (a + b * γ) ((a : ℂ) • ρ + (b : ℂ) • σ) ρ = b * E γ σ ρ

lemma c12_mixture_cutoffs {n : ℕ} (ρ σ : Mat n)
    (hρ : StrictDensity ρ) (hσ : StrictDensity σ) (R : ℝ) (hR : 1 ≤ R)
    (hρσ : ρ ≤ (R : ℂ) • σ) (hσρ : σ ≤ (R : ℂ) • ρ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    1 ≤ R / (b + a * R) ∧ R / (b + a * R) ≤ R ∧
      1 ≤ a + b * R ∧ a + b * R ≤ R ∧
      ρ ≤ ((R / (b + a * R) : ℝ) : ℂ) • ((a : ℂ) • ρ + (b : ℂ) • σ) ∧
      (a : ℂ) • ρ + (b : ℂ) • σ ≤ ((a + b * R : ℝ) : ℂ) • ρ

lemma c12_integral_truncate_zero_tail (f : ℝ → ℝ) (L R : ℝ)
    (hL : 1 ≤ L) (hLR : L ≤ R)
    (hf : ContinuousOn f (Set.Icc (1 : ℝ) R))
    (hzero : ∀ v : ℝ, L ≤ v → f v = 0) :
    (∫ v in (1 : ℝ)..R, f v) = ∫ v in (1 : ℝ)..L, f v

lemma c12_change_variable_forward (f : ℝ → ℝ) (a b R : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hR : 1 ≤ R)
    (hf : ContinuousOn f (Set.Icc (1 : ℝ) (R / (b + a * R)))) :
    (∫ v in (1 : ℝ)..(R / (b + a * R)), f v) =
      ∫ γ in (1 : ℝ)..R, f (γ / (b + a * γ)) * (b / (b + a * γ) ^ 2)

lemma c12_change_variable_reverse (f : ℝ → ℝ) (a b R : ℝ)
    (hb : 0 < b) (hab : a + b = 1) (hR : 1 ≤ R)
    (hf : ContinuousOn f (Set.Icc (1 : ℝ) (a + b * R))) :
    (∫ v in (1 : ℝ)..(a + b * R), f v) =
      ∫ γ in (1 : ℝ)..R, f (a + b * γ) * b

lemma c12_relative_entropy_mixture_finite {n : ℕ} (hn : 1 ≤ n) (ρ σ : Mat n)
    (hρ : StrictDensity ρ) (hσ : StrictDensity σ) (R : ℝ) (hR : 1 ≤ R)
    (hρσ : ρ ≤ (R : ℂ) • σ) (hσρ : σ ≤ (R : ℂ) • ρ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    IntervalIntegrable
      (fun γ : ℝ => b ^ 2 * E γ ρ σ / (γ * (b + a * γ) ^ 2) +
        b ^ 2 * E γ σ ρ / (a + b * γ) ^ 2) MeasureTheory.volume 1 R ∧
      relEntropy ρ ((a : ℂ) • ρ + (b : ℂ) • σ) =
        ∫ γ in (1 : ℝ)..R,
          b ^ 2 * E γ ρ σ / (γ * (b + a * γ) ^ 2) +
          b ^ 2 * E γ σ ρ / (a + b * γ) ^ 2
```

## Unchanged frozen final contract

```lean
theorem weighted_entropy_finite_kernel {n : ℕ} (hn : 1 ≤ n) (ρ σ : Mat n)
    (hρ : StrictDensity ρ) (hσ : StrictDensity σ) (R : ℝ) (hR : 1 ≤ R)
    (hρσ : ρ ≤ (R : ℂ) • σ) (hσρ : σ ≤ (R : ℂ) • ρ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    IntervalIntegrable
      (fun γ : ℝ => kernelAB a b γ * E γ ρ σ + kernelBA a b γ * E γ σ ρ)
      MeasureTheory.volume 1 R ∧
      chi a b ρ σ = ∫ γ in (1 : ℝ)..R,
        kernelAB a b γ * E γ ρ σ + kernelBA a b γ * E γ σ ρ
```

## Exact route, finite cutoffs and endpoint checks

Strict density of the positive mixture is derived from positive definiteness
and actual complex trace, with no conditioning assumption. The chi identity
is literal trace linearity and distributes the right-hand logarithm; it holds
for arbitrary matrices under the existing totalized definitions, so its lack
of positivity hypotheses is deliberate. It never commutes matrix products.

Put M=a*rho+b*sigma, L=R/(b+aR), U=a+bR. Both L and U lie in [1,R],
since a,b>0 and a+b=1. From rho <= R*sigma we get
(b+aR)*rho <= R*M, and from sigma <= R*rho we get M <= U*rho.
Thus the same original R is a valid two-sided cutoff for (rho,M).
After applying the internally proved C11 to (rho,M), split its two continuous
integrands. The first is zero for every v>=L and the second for every v>=U.
Truncate them separately to [1,L] and [1,U] BEFORE substitution.

The forward substitution v=gamma/(b+a*gamma) has positive derivative
b/(b+a*gamma)^2 and maps [1,R] to [1,L]; its denominator is strictly positive
on the complete closed interval. The reverse substitution v=a+b*gamma has
derivative b and maps [1,R] to [1,U]. Positive-part homogeneity gives the
explicit two E identities, hence the two displayed b^2 weights. R=1 yields
zero-length intervals throughout; no denominator is zero and no limiting
argument is used. Repeated spectra and noncommuting matrices remain allowed.

Exchange (rho,a) and (sigma,b) for the second relative entropy. After multiplying
by a and b and using trace linearity, the two coefficients simplify exactly to
kernelAB and kernelBA. Continuous integrands on the fixed compact [1,R]
supply all required Bochner interval-integrability proofs. No numerical
quadrature, assumed C11, altered log/entropy definition, stronger cutoff, or
hidden matrix inequality is permitted. C11 is currently in actual local
proof development and will be an internal proved import, never an axiom.

The symbolic route comes from Sidney Holden's existing complete MI27
manuscript, section3, with explicit finite-cutoff details from the frozen
contract. Frenkel and Hirche--Tomamichel retain integral-identity credit;
George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, is the formalization contributor.

Implementation will begin only after the two nonauthor statement reviews.
All run results will be recorded separately. Whole MI27 remains incomplete.
