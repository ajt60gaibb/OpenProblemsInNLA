# MI27 C11: from negative counts to the pencil integral, before bodies

Author `/root/nr04_mf14_final_referee_a`; source-only work, root alone compiles.
The following six exact helper headers have no bodies yet. This is a proposed
next statement gate for root and an independent nonauthor referee. No earlier
definition or approved header is changed, and the frozen full C11 remains the
target. The two trace-one inputs and finite cutoff will only be specialized
after the general positive-definite pencil formula is established.

## Exact headers

Namespace `NLA.MI27`; open MeasureTheory and scoped BigOperators, Classical,
ComplexOrder, MatrixOrder, Matrix, and Matrix.Norms.L2Operator. All count,
weight, trace, logarithm, entropy, and identity-shift definitions below are
the already fixed literal definitions. No new definition is proposed.

```lean
lemma c11_posDef_normalizer {n : ℕ} (P : Mat n) (hP : P.PosDef) :
    ∃ S : Mat n, IsUnit S ∧ Sᴴ * P * S = 1

lemma c11_negativeCount_affine_identity_spectral {n : ℕ} (hn : 1 ≤ n)
    (C : Mat n) (hC : C.IsHermitian) (t : ℝ) :
    c11_negativeCount (1 + (t : ℂ) • C) =
      ∑ i : Fin n, if 1 + t * hC.eigenvalues i < 0 then (1 : ℝ) else 0

lemma c11_normalized_pencil_count_integral {n : ℕ} (hn : 1 ≤ n)
    (C : Mat n) (hC : C.IsHermitian) (h1C : (1 + C).PosDef) :
    MeasureTheory.Integrable
      (fun t : ℝ => c11_pencilWeight t * c11_negativeCount (1 + (t : ℂ) • C)) ∧
      (∫ t : ℝ, c11_pencilWeight t * c11_negativeCount (1 + (t : ℂ) • C)) =
        trR (logM (1 + C)) - trR (C * (1 + C)⁻¹)

lemma c11_shifted_pencil_count_integral {n : ℕ} (hn : 1 ≤ n)
    (X Y : Mat n) (hX : X.PosDef) (hY : Y.PosDef) (r : ℝ) (hr : 0 ≤ r) :
    MeasureTheory.Integrable
      (fun t : ℝ => c11_pencilWeight t *
        c11_negativeCount (c11_identityShift (X + (t : ℂ) • (Y - X)) r)) ∧
      (∫ t : ℝ, c11_pencilWeight t *
        c11_negativeCount (c11_identityShift (X + (t : ℂ) • (Y - X)) r)) =
        c11_shiftKernel X Y hX.isHermitian hY.isHermitian r

lemma c11_pencil_count_integrable_prod {n : ℕ} (hn : 1 ≤ n)
    (X Y : Mat n) (hX : X.PosDef) (hY : Y.PosDef) :
    MeasureTheory.Integrable
      (fun z : ℝ × ℝ => c11_pencilWeight z.2 *
        c11_negativeCount (c11_identityShift (X + (z.2 : ℂ) • (Y - X)) z.1))
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod MeasureTheory.volume)

lemma c11_relative_entropy_pencil_integral {n : ℕ} (hn : 1 ≤ n)
    (X Y : Mat n) (hX : X.PosDef) (hY : Y.PosDef) :
    MeasureTheory.Integrable
      (fun t : ℝ => c11_pencilWeight t * tracePos (-(X + (t : ℂ) • (Y - X)))) ∧
      relEntropy X Y - trR (X - Y) =
        ∫ t : ℝ, c11_pencilWeight t * tracePos (-(X + (t : ℂ) • (Y - X)))
```

## Concrete mathematical route

For the normalizer, set S=P^(-1/2) in the existing continuous functional
calculus. P>0 implies S is positive, Hermitian, and invertible. The pinned
`CFC.conjugate_rpow_neg_one_half` is exactly S P S = I. This existence claim
includes n=0; the later spectral trace helpers retain the frozen n≥1 premise.

For affine identity pencils, finite-spectrum CFC composition for
x ↦ 1+t*x gives the strict negative count as the displayed sum. This is
valid at every real t, including t=0, and with repeated or zero eigenvalues.
It requires no continuity of the strict indicator away from the finite
spectrum. Its strict inequality excludes exactly the zero eigenvalues.

The already reviewed trace-log spectral bridge gives c_i>-1 when I+C>0.
The actual scalar pencil-count integral applies separately to each c_i,
including c_i=0 and -1<c_i<0. Finite summation therefore establishes both
integrability and the normalized trace-log/resolvent integral. There is no
interchange of infinite sums in this step.

At each fixed r≥0, put P=X+rI, Q=Y+rI, take the normalizer S for P, and set
C=Sᴴ(Y-X)S. Direct algebra yields I+C=SᴴQS>0 and
Sᴴ(X+t(Y-X)+rI)S=I+tC for every real t. The root-owned congruence-inertia
lemma identifies the two strict counts, including all singular pencil
values. The normalized count integral and the reviewed normalized trace
kernel identity give the shifted pencil-count integral. Neither a
simultaneous eigenbasis nor a pointwise positive-trace congruence is used.

For the exchange of integrals, write
G(r,t)=w(t) count(X+t(Y-X)+rI), with r integrated over (0,infinity) and t
over the whole real line. G is nonnegative everywhere because w≥0 and
the actual strict count is nonnegative. It is jointly measurable by the
already compiled pencil-count measurability result, coordinate swap, and
the measurable rational weight. The weight is the totalized literal
1/(|t|*(t-1)^2); its values at 0 and 1 are zero, which presents no measure
or singular-endpoint exception.

`MeasureTheory.integrable_prod_iff` reduces actual Bochner product
integrability to almost-everywhere integrable t-sections and integrability
of r ↦ ∫ |G(r,t)| dt. Every section with r>0 is integrable by the previous
helper. Nonnegativity removes the absolute value, and that inner integral
is the compiled shift kernel. Its integrability on r>0 is already proved
by `c11_shiftKernel_integral_Ioi`. Thus the product is integrable before
Fubini is used; integrability is not assumed from a desired entropy formula.

Now `Integrable.integral_prod_right` and `integral_integral_swap` apply.
For every t, the already compiled negative-count layer cake says
∫_{r>0} count(X+t(Y-X)+rI) dr = tracePos(-(X+t(Y-X))). Multiplication by
the fixed scalar w(t) yields the inner r-integral. The other order is
the shift-kernel integral, equal to D(X||Y)-trR(X-Y). This gives precisely
the stated general pencil integral and its integrability. The trace
correction is deliberately retained until trace-one specialization.

## Pinned reuse and scope

Pin remains `0df444a360eaa60ab8c11dca51a86af692955474`.
Relevant primary APIs read locally: `CFC.conjugate_rpow_neg_one_half`,
`IsStrictlyPositive.rpow`, `cfc_const_mul_id`, `cfc_const_add`, `cfc_comp'`,
`MeasureTheory.integrable_prod_iff`, `Integrable.integral_prod_right`, and
`MeasureTheory.integral_integral_swap`. Existing project dependencies are
the scalar pencil integral, the trace-log component, the shared negative
count, its full joint measurability and layer cake, and the actual improper
identity-shift integral. The congruence-inertia source is root-owned and
will only be used after its successful source-matched local verification.

These six helpers would supply the general Frenkel pencil representation.
They do not by themselves prove the exact finite hockey-stick statement.
The t<0 and t>1 substitutions, trace-one specialization, and supplied
common Loewner cutoff remain separate obligations. There is no completed
original target, no count increment, and no Lean or Comparator execution
claimed by this source author.
