# MI27 C11: exact changes of variables and finite cutoff, before bodies

Author `/root/nr04_mf14_final_referee_a`; source-only development, root alone
compiles. These eight new helper headers have no bodies yet and require
root plus independent nonauthor statement review. The last header below
is the unchanged, already frozen C11 contract; it is included to make the
final assembly and scope explicit. No definition is added or changed.

## Exact new helper headers

Namespace `NLA.MI27`; open MeasureTheory and scoped BigOperators, Classical,
ComplexOrder, MatrixOrder, Matrix, and Matrix.Norms.L2Operator.

```lean
lemma c11_tracePos_smul_nonneg {n : ℕ} (M : Mat n) (hM : M.IsHermitian)
    (a : ℝ) (ha : 0 ≤ a) :
    tracePos ((a : ℂ) • M) = a * tracePos M

lemma c11_pencil_tracePos_zero_unit_interval {n : ℕ} (X Y : Mat n)
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    tracePos (-(X + (t : ℂ) • (Y - X))) = 0

lemma c11_change_variable_pencil_positive (f : ℝ → ℝ) :
    (MeasureTheory.IntegrableOn f (Set.Ioi (1 : ℝ)) ↔
      MeasureTheory.IntegrableOn
        (fun γ : ℝ => f (γ / (γ - 1)) / (γ - 1) ^ 2) (Set.Ioi (1 : ℝ))) ∧
      (∫ t in Set.Ioi (1 : ℝ), f t) =
        ∫ γ in Set.Ioi (1 : ℝ), f (γ / (γ - 1)) / (γ - 1) ^ 2

lemma c11_change_variable_pencil_negative (f : ℝ → ℝ) :
    (MeasureTheory.IntegrableOn f (Set.Iio (0 : ℝ)) ↔
      MeasureTheory.IntegrableOn
        (fun γ : ℝ => f (-1 / (γ - 1)) / (γ - 1) ^ 2) (Set.Ioi (1 : ℝ))) ∧
      (∫ t in Set.Iio (0 : ℝ), f t) =
        ∫ γ in Set.Ioi (1 : ℝ), f (-1 / (γ - 1)) / (γ - 1) ^ 2

lemma c11_pencil_integrand_positive_substitution {n : ℕ} (X Y : Mat n)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (γ : ℝ) (hγ : 1 < γ) :
    (c11_pencilWeight (γ / (γ - 1)) *
      tracePos (-(X + ((γ / (γ - 1) : ℝ) : ℂ) • (Y - X)))) / (γ - 1) ^ 2 =
        E γ X Y / γ

lemma c11_pencil_integrand_negative_substitution {n : ℕ} (X Y : Mat n)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (γ : ℝ) (hγ : 1 < γ) :
    (c11_pencilWeight (-1 / (γ - 1)) *
      tracePos (-(X + ((-1 / (γ - 1) : ℝ) : ℂ) • (Y - X)))) / (γ - 1) ^ 2 =
        E γ Y X / γ ^ 2

lemma c11_relative_entropy_hockey_stick_Ioi {n : ℕ} (hn : 1 ≤ n)
    (X Y : Mat n) (hX : X.PosDef) (hY : Y.PosDef) :
    MeasureTheory.IntegrableOn
      (fun γ : ℝ => E γ X Y / γ + E γ Y X / γ ^ 2) (Set.Ioi (1 : ℝ)) ∧
      relEntropy X Y - trR (X - Y) =
        ∫ γ in Set.Ioi (1 : ℝ), E γ X Y / γ + E γ Y X / γ ^ 2

lemma c11_integral_Ioi_eq_interval_of_zero_tail (f : ℝ → ℝ) (R : ℝ) (hR : 1 ≤ R)
    (hf : MeasureTheory.IntegrableOn f (Set.Ioi (1 : ℝ)))
    (hzero : ∀ γ : ℝ, R ≤ γ → f γ = 0) :
    (∫ γ in Set.Ioi (1 : ℝ), f γ) = ∫ γ in (1 : ℝ)..R, f γ
```

## Frozen final contract, unchanged

```lean
theorem relative_entropy_finite_hockey_stick {n : ℕ} (hn : 1 ≤ n) (ρ σ : Mat n)
    (hρ : StrictDensity ρ) (hσ : StrictDensity σ) (R : ℝ) (hR : 1 ≤ R)
    (hρσ : ρ ≤ (R : ℂ) • σ) (hσρ : σ ≤ (R : ℂ) • ρ) :
    IntervalIntegrable (fun γ : ℝ => E γ ρ σ / γ + E γ σ ρ / γ ^ 2)
      MeasureTheory.volume 1 R ∧
      relEntropy ρ σ =
        ∫ γ in (1 : ℝ)..R, E γ ρ σ / γ + E γ σ ρ / γ ^ 2
```

## Mathematical route and endpoint checks

Positive-part homogeneity follows from finite-spectrum CFC composition and
max(a*x,0)=a*max(x,0) for a≥0, followed by the actual trace. This includes
a=0 and n=0; neither a matrix norm nor an alternative trace is substituted.
For 0≤t≤1, the pencil is (1-t)X+tY≥0. Its negative has zero positive part,
so the weighted pencil integrand vanishes throughout the closed interval.

On γ>1 define T(γ)=γ/(γ-1)=1+1/(γ-1). It is a differentiable bijection
from (1,infinity) to itself with inverse T and derivative -1/(γ-1)^2.
Define N(γ)=-1/(γ-1). It is a differentiable bijection from (1,infinity)
to (-infinity,0), inverse γ=1-1/t, and derivative 1/(γ-1)^2.
Both absolute Jacobians are 1/(γ-1)^2. The two generic change-of-variable
statements follow from the pinned one-dimensional Jacobian theorem for
an injective differentiable map on a measurable set, including its exact
integrability equivalence. They require no extra hypothesis on f: the
library's Bochner integral and integrability equivalence apply to arbitrary
f. No substitution evaluates a singular endpoint inside its open domain.

For T, direct algebra yields
-(X+T(γ)(Y-X))=(1/(γ-1))(X-γY). The coefficient is positive. Homogeneity,
w(T)=1/(T*(T-1)^2), and the absolute Jacobian give exactly E(γ,X,Y)/γ.
For N the analogous identity is
-(X+N(γ)(Y-X))=(1/(γ-1))(Y-γX). Since N<0, the absolute value in w(N)
is -N. Homogeneity and the Jacobian give exactly E(γ,Y,X)/γ^2. Every scalar
denominator is nonzero because γ>1. Matrix multiplication is never commuted.

The proved general pencil integrability restricts to t<0 and t>1.
The two integrability equivalences and pointwise formulas give both
hockey-stick summands integrable on γ>1. Split the full real-line pencil
integral into those two tails and the zero central interval; singleton
endpoints have zero Lebesgue measure. Apply the two change-of-variable
identities and integral additivity. This yields the seventh helper with
the general trace correction still present.

For the final cutoff lemma, `intervalIntegral.integral_Ioi_sub_Ioi` with
1≤R says that the interval integral equals the Ioi(1) integral minus the
Ioi(R) tail. The tail is identically zero by hzero. The case R=1 is included
and does not require a strict inequality or a limiting argument.

To assemble the frozen C11, use the already compiled finite integrability
helper, specialize the new improper formula to the actual StrictDensity
inputs, cancel trR(ρ-σ) using their literal complex trace-one equalities,
and use the existing compiled two-sided Loewner zero-tail helper with the
original supplied R. The separate existing R=1 theorem may also be reused.
There is no commuting-input premise, larger substitute cutoff, altered
relative entropy definition, assumed full integral identity, or weakened
coefficient. C12 is not used as a premise.

## Pinned APIs and remaining status

Mathlib pin `0df444a360eaa60ab8c11dca51a86af692955474`:
`MeasureTheory/Function/JacobianOneDim.lean` supplies
`integrableOn_image_iff_integrableOn_abs_deriv_smul` and
`integral_image_eq_integral_abs_deriv_smul`. Scalar derivative rules and
exact field arithmetic establish the two Jacobians. `Integral/Bochner/Set`
and `Integral/IntervalIntegral/Basic` supply the interval partitions,
zero-set integrals, and Ioi subtraction identity. The actual existing
FiniteHockeyStick source supplies finite integrability and zero tails.

This document contains no bodies and does not claim a completed proof or
run. The preceding general pencil-integral component is source-complete
and pending actual root-controlled compilation. Full original C11 becomes
locally established only after the unchanged final theorem actually
compiles and its trust audits pass; whole MI27 still has other contracts
to complete and ultimately independent final reviews and Linux Comparator.
