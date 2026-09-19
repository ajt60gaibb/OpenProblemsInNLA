# MI27 C11: scalar pencil integrals, before implementation

This extends the root-approved negative-count plan. No proof bodies for
these new headers have been written. Author `/root/nr04_mf14_final_referee_a`
will work source-only; root alone runs Lean. The frozen C11 target, all
earlier helper headers, and all original matrix definitions remain unchanged.

For P=X+rI>0, congruence will replace the pencil by I+tC with I+C>0.
Thus the scalar eigenvalue parameter c ranges over the entire interval
c>-1, including negative, zero, and repeated eigenvalues. The required
scalar formula integrates the strict indicator of 1+t*c<0 against the
literal Frenkel weight. This is independent of the matrix congruence proof
and can be developed while that algebraic obligation is separate.

The primitive below is written using q(t)=1/(t-1): log(1+q)-q. This form
has an immediate zero limit at both infinite ends, since q tends to zero
and log is continuous at 1. Away from t=0,1 its derivative is
1/(t*(t-1)^2). For t>1 this is the actual weight; for t<0 the derivative
of its negative is the weight. Both tail integrals therefore equal the
negative of the primitive at their finite endpoint. Real division and log
are totalized in the definitions, but the derivative and tail statements
explicitly exclude the singular points.

## Exact definitions and headers

Namespace `NLA.MI27`; open Filter, Set, MeasureTheory and scoped Topology.

```lean
def c11_pencilWeight (t : ℝ) : ℝ := 1 / (|t| * (t - 1) ^ 2)

def c11_pencilPrimitive (t : ℝ) : ℝ :=
  Real.log (1 + 1 / (t - 1)) - 1 / (t - 1)

lemma c11_pencilWeight_nonneg (t : ℝ) : 0 ≤ c11_pencilWeight t

lemma c11_hasDerivAt_pencilPrimitive (t : ℝ) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    HasDerivAt c11_pencilPrimitive (1 / (t * (t - 1) ^ 2)) t

lemma c11_tendsto_pencilPrimitive :
    Filter.Tendsto c11_pencilPrimitive Filter.atTop (nhds 0) ∧
      Filter.Tendsto c11_pencilPrimitive Filter.atBot (nhds 0)

lemma c11_pencilWeight_integral_positive_tail (a : ℝ) (ha : 1 < a) :
    MeasureTheory.IntegrableOn c11_pencilWeight (Set.Ioi a) ∧
      (∫ t in Set.Ioi a, c11_pencilWeight t) = -c11_pencilPrimitive a

lemma c11_pencilWeight_integral_negative_tail (a : ℝ) (ha : a < 0) :
    MeasureTheory.IntegrableOn c11_pencilWeight (Set.Iio a) ∧
      (∫ t in Set.Iio a, c11_pencilWeight t) = -c11_pencilPrimitive a

lemma c11_pencilPrimitive_at_threshold (c : ℝ) (hc : -1 < c) (hc0 : c ≠ 0) :
    -c11_pencilPrimitive (-1 / c) = Real.log (1 + c) - c / (1 + c)

lemma c11_scalar_pencil_count_integral (c : ℝ) (hc : -1 < c) :
    MeasureTheory.Integrable
      (fun t : ℝ => c11_pencilWeight t * (if 1 + t * c < 0 then (1 : ℝ) else 0)) ∧
      (∫ t : ℝ, c11_pencilWeight t * (if 1 + t * c < 0 then (1 : ℝ) else 0)) =
        Real.log (1 + c) - c / (1 + c)
```

For c>0 the strict indicator is exactly the indicator of (-infinity,-1/c),
with -1/c<0. For -1<c<0 it is the indicator of (-1/c,infinity), with
-1/c>1. For c=0 the integrand and formula are zero. Threshold points have
zero Lebesgue mass and are excluded by the strict inequality as required.
The threshold primitive evaluation follows from
1/(-1/c-1)=-c/(1+c), 1-c/(1+c)=1/(1+c), and log(1/u)=-log u for u>0.

## Pinned API route and scope

The derivative uses existing scalar logarithm/reciprocal rules, with exact
field arithmetic and explicit nonzero denominator proofs. The positive
tail uses `MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'` and
`MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'`, already used in the
compiled identity-shift component. The negative tail can be reflected to
Ioi(-a), where the derivative of primitive(-t) is weight(-t); Lebesgue
negation preserves measure. Relevant pinned APIs inspected include
`MeasurePreserving.integrableOn_comp_preimage`, `Measure.measurePreserving_neg`,
`integral_comp_neg_Ioi`, and the equality of Iic and Iio integrals under
nonatomic Lebesgue measure. The final strict indicator uses
`integrable_indicator_iff` and `integral_indicator` as in the count layer cake.
Mathlib pin remains `0df444a360eaa60ab8c11dca51a86af692955474`.

This is only the scalar component of the previously documented count/Tonelli
route. It does not assert matrix inertia, trace-log determinant algebra,
the joint Tonelli exchange, the full pencil identity, or C11. Those remain
separate formal obligations. No target count changes and no Lean or
Comparator run are claimed.
