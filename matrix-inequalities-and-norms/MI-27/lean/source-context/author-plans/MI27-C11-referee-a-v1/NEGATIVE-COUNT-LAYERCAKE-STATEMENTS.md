# MI27 C11: negative-count layer-cake statements, before implementation

Recorded 2026-09-19 by MI27 source author `/root/nr04_mf14_final_referee_a`.
This is a new helper gate. The two earlier approved plans and their twelve
compiled headers remain unchanged. No body for any lemma below has been
written. Root alone runs the one-thread, 4096 MiB local Lean compiler.

## Original target and current boundary

The unchanged C11 contract in the frozen Challenge is the full ordinary
Umegaki identity for arbitrary, possibly noncommuting, strictly positive
density matrices, with the given common Loewner cutoff R >= 1. Challenge
SHA256 is `1cacb3aa3088860016b9d121904677d56c6c8e6025de9eeaf262957c2bc0d640`.
No C12 premise, commutativity, distinct-eigenvalue assumption, or extra
conclusion-shaped hypothesis is introduced. The existing actual local
091/092 runs prove the shift-kernel half-line integral, including the
necessary `trR (X - Y)` correction before trace normalization. They do not
prove the pencil/hockey-stick connection.

## Concrete route to the full connection

Write Delta = Y-X and A(t) = X+t Delta. For each Hermitian M define nu(M) as
the number of its strictly negative eigenvalues, counting multiplicity.
Then tr((-M)_+) = integral_(r>0) nu(M+rI) dr. The immediate helper scope
below establishes this equality as an actual integrable real Bochner
integral, plus joint measurability for M=A(t). It includes singular M and
zero eigenvalues. It uses no varying eigenbasis or differentiability of
individual eigenvalues.

For the later algebraic step, fix r >= 0, put P=X+rI, Q=Y+rI, and
C=P^(-1/2) Delta P^(-1/2). Positive definiteness gives I+C>0, so every
eigenvalue c of C satisfies c>-1. Hermitian congruence gives

    nu(A(t)+rI) = nu(I+tC).

Only negative counts are invariant under this congruence. The eigenvalues
themselves and their negative-part sum are not asserted invariant. With
w(t)=1/(|t|*(t-1)^2), exact one-variable integration gives

    integral_R w(t) * 1_{1+t*c<0} dt
      = log(1+c) - c/(1+c),       c>-1.

The c>0 branch has support t<-1/c; the -1<c<0 branch has support t>-1/c;
the c=0 branch is zero. Both integrals use the primitive
log|t|-log|t-1|-1/(t-1), with the appropriate sign of |t|. Repeated c and
zero c are retained. Thus the inner t integral becomes

    tr(log(I+C)) - tr(C*(I+C)^(-1))
      = tr(log Q)-tr(log P)-tr(Delta*Q^(-1))
      = c11_shiftKernel X Y hX.isHermitian hY.isHermitian r.

The first trace equality requires actual determinant/trace-log and cyclic
trace/inverse algebra; it is not a matrix-log congruence identity. The
last equality follows from the already used two individual spectral bases
and their unitary-overlap marginals. Nonnegative Tonelli then exchanges t
and r, and the already compiled improper integral yields

    integral_R w(t)*tracePos(-A(t)) dt
      = relEntropy X Y - trR(X-Y).

For densities the trace correction is zero. Positivity makes the integrand
zero on [0,1]. On t>1 substitute gamma=t/(t-1); on t<0 substitute
gamma=(t-1)/t. Positive homogeneity gives respectively E gamma X Y/gamma
and E gamma Y X/gamma^2. Existing FiniteHockeyStick removes the tails past
the supplied R and handles R=1. These substitutions and all remaining
algebraic/measure obligations still require formal proofs.

## Immediate transparent definitions and exact helper headers

All declarations are in `NLA.MI27`, with the existing actual `Mat`, `trR`,
`tracePos`, and `c11_identityShift`. Scopes are BigOperators, Classical,
ComplexOrder, MatrixOrder, Matrix, Matrix.Norms.L2Operator, and Topology.
The eigenvalue count is a finite-spectrum CFC of the literal strict-step
function. Although the step function is discontinuous on R, its restriction
to each finite spectrum is continuous; no discontinuous global CFC theorem
is assumed. These definitions contain no target equality.

```lean
def c11_negativeCount {n : ℕ} (M : Mat n) : ℝ :=
  trR (cfc (fun x : ℝ => if x < 0 then 1 else 0) M)

def c11_negativeCountApprox {n : ℕ} (M : Mat n) (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) *
    (tracePos (-M) -
      tracePos (-(c11_identityShift M (1 / ((k : ℝ) + 1)))))

lemma c11_cfc_function_identityShift {n : ℕ} (M : Mat n)
    (hM : M.IsHermitian) (f : ℝ → ℝ) (r : ℝ) :
    cfc f (c11_identityShift M r) = cfc (fun x : ℝ => f (x + r)) M

lemma c11_negativeCount_spectral {n : ℕ} (hn : 1 ≤ n) (M : Mat n)
    (hM : M.IsHermitian) :
    c11_negativeCount M =
      ∑ i : Fin n, if hM.eigenvalues i < 0 then (1 : ℝ) else 0

lemma c11_negativeCount_bounds {n : ℕ} (hn : 1 ≤ n) (M : Mat n)
    (hM : M.IsHermitian) :
    0 ≤ c11_negativeCount M ∧ c11_negativeCount M ≤ (n : ℝ)

lemma c11_negativeCount_identityShift {n : ℕ} (hn : 1 ≤ n) (M : Mat n)
    (hM : M.IsHermitian) (r : ℝ) :
    c11_negativeCount (c11_identityShift M r) =
      ∑ i : Fin n, if hM.eigenvalues i + r < 0 then (1 : ℝ) else 0

lemma c11_tracePos_neg_identityShift {n : ℕ} (hn : 1 ≤ n) (M : Mat n)
    (hM : M.IsHermitian) (r : ℝ) :
    tracePos (-(c11_identityShift M r)) =
      ∑ i : Fin n, max (-(hM.eigenvalues i + r)) 0

lemma c11_integral_negative_indicator (x : ℝ) :
    MeasureTheory.IntegrableOn
      (fun r : ℝ => if x + r < 0 then (1 : ℝ) else 0) (Set.Ioi 0) ∧
      (∫ r in Set.Ioi (0 : ℝ), if x + r < 0 then (1 : ℝ) else 0) = max (-x) 0

lemma c11_negativeCount_shift_integral {n : ℕ} (hn : 1 ≤ n) (M : Mat n)
    (hM : M.IsHermitian) :
    MeasureTheory.IntegrableOn
      (fun r : ℝ => c11_negativeCount (c11_identityShift M r)) (Set.Ioi 0) ∧
      (∫ r in Set.Ioi (0 : ℝ), c11_negativeCount (c11_identityShift M r)) =
        tracePos (-M)

lemma c11_scalar_negativeCountApprox_eventually (x : ℝ) :
    ∀ᶠ k : ℕ in Filter.atTop,
      ((k : ℝ) + 1) * (max (-x) 0 - max (-(x + 1 / ((k : ℝ) + 1))) 0) =
        if x < 0 then (1 : ℝ) else 0

lemma c11_negativeCountApprox_eventually {n : ℕ} (hn : 1 ≤ n) (M : Mat n)
    (hM : M.IsHermitian) :
    ∀ᶠ k : ℕ in Filter.atTop, c11_negativeCountApprox M k = c11_negativeCount M

lemma c11_tracePos_continuous_comp {n : ℕ} (hn : 1 ≤ n)
    {α : Type*} [TopologicalSpace α] (F : α → Mat n)
    (hF : Continuous F) (hFH : ∀ x, (F x).IsHermitian) :
    Continuous (fun x => tracePos (F x))

lemma c11_negativeCount_pencil_measurable {n : ℕ} (hn : 1 ≤ n) (X Y : Mat n)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    Measurable (fun z : ℝ × ℝ =>
      c11_negativeCount
        (c11_identityShift (X + (z.1 : ℂ) • (Y - X)) z.2))
```

The approximation is eventually exact at every fixed Hermitian matrix:
negative eigenvalues eventually exceed the reciprocal step in absolute
value, while zero and positive eigenvalues contribute zero for every step.
C07 supplies continuity of tracePos along continuous Hermitian families.
Consequently each approximation along the two-variable pencil is continuous,
and the sequential pointwise limit is measurable. This proof avoids relying
on continuity or measurable selection of a chosen eigenbasis.

The scalar indicator integral is the volume of (0,-x), whose real volume
is max(-x,0). Finite summation and the actual CFC spectral formulas then give
the matrix layer cake, including all signs and multiplicities.

## Smallest independent algebraic obligation

Once `c11_negativeCount` is shared, another author can independently prove
the following exact statement; this file does not provide or assume its body.

```lean
lemma c11_negativeCount_congruence {n : ℕ} (hn : 1 ≤ n) (M S : Mat n)
    (hM : M.IsHermitian) (hS : IsUnit S) :
    c11_negativeCount (Sᴴ * M * S) = c11_negativeCount M
```

M may be singular. The hypothesis is matrix-ring invertibility of S. A
possible route is the maximal dimension of a negative definite subspace,
transported by S. Mathlib's real quadratic-form signature invariance gives
an alternative route after constructing the underlying real quadratic form
Re(v* M v) and proving its negative signature is twice this complex count.
Complex bilinear quadratic forms cannot substitute for Hermitian forms.
No ready-made complex Hermitian inertia theorem was found in the bounded
inspection, so either bridge is a genuine remaining obligation.

## Exact downstream checkpoint (not immediate implementation scope)

The following transparent weight and lemma specify the missing integrated
pencil-to-kernel interface. They are a checkpoint, not a new axiom or an
input hypothesis to C11. Root may assign its components independently after
the preceding count definition is frozen.

```lean
def c11_pencilWeight (t : ℝ) : ℝ := 1 / (|t| * (t - 1) ^ 2)

lemma c11_pencil_count_integral {n : ℕ} (hn : 1 ≤ n) (X Y : Mat n)
    (hX : X.PosDef) (hY : Y.PosDef) (r : ℝ) (hr : 0 ≤ r) :
    MeasureTheory.Integrable (fun t : ℝ => c11_pencilWeight t *
      c11_negativeCount (c11_identityShift (X + (t : ℂ) • (Y - X)) r)) ∧
      (∫ t : ℝ, c11_pencilWeight t *
        c11_negativeCount (c11_identityShift (X + (t : ℂ) • (Y - X)) r)) =
        c11_shiftKernel X Y hX.isHermitian hY.isHermitian r
```

Totalized real division sets w(0)=w(1)=0. The actual count is zero near both
points for each r>=0 and positive definite X,Y, so this convention introduces
no singular-point assumption and does not change the integral.

## Primary sources and pinned API inspection

The mathematical source was re-read at
[Frenkel, arXiv:2208.12194v4, Sections 3-4 and Theorem 6](https://arxiv.org/html/2208.12194v4).
His proof uses the determinant pencil, residues and eigenvalue arcs. The
count/Tonelli route above is a separately reasoned implementation route to
the same representation; no claim is made that it is already in Mathlib.
[Hirche and Tomamichel, arXiv:2306.12343v3, Corollary 2.3](https://arxiv.org/html/2306.12343v3)
supplies the two changes of variable and the ordered hockey-stick weights.

Bounded read-only API inspection at Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474` covered:

- finite-spectrum CFC composition, `cfc_neg_id`, and the retained C02 proof;
- C07 positive-part Lipschitz and the retained continuous-gamma proof;
- `integrable_indicator_iff`, `integrableOn_indicator_iff`,
  `integral_indicator_one`, `Real.volume_real_Ioo`;
- `measurable_of_tendsto_metrizable`, which takes a sequential pointwise
  limit expressed using the function-space neighborhood filter;
- `QuadraticMap.Equivalent.sigNeg_eq` and the maximal-subspace definition
  of `QuadraticMap.sigNeg` in `LinearAlgebra/QuadraticForm/Signature.lean`;
- Hermitian determinant/trace spectral formulas and positive determinant.

No Lean or Comparator run was performed by this author. No source proof of
the new headers is claimed. Full C11 and the original target remain open in
this development; the completed-original-target count increment is zero.
