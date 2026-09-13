# RA-09: complete-target statement-first feasibility note

Prepared by `/root/solved_statement_inventory`, 12 September 2026 (America/New_York).

**Assessment: feasible, with a moderate generic algebra/finite-spectrum implementation.** The complete source supplies an affirmative proof. No missing Schatten, exterior-power, integration or pseudoinverse foundation is necessary. The main work is a scalar inequality, honest finite spectral expansions and a harmonic constraint obtained directly from an actual PSD matrix. This is a feasibility plan: no Lean statement package was created, no statements were typechecked, and no proof was implemented or approved.

I read the complete canonical RA-09 page and complete reviewed manuscript, including its unordered theorem and degenerate cases, plus the full independent informal review. The read-only source snapshot is `5830ed4fb06da0659414a3deb2a40ad327aca052`, accessed through existing Git objects in `/tmp/nla-lean-ra08-worktree`. RA-09 is `Solved` and has no Lean project at that snapshot. This is not a new public-fork or current-network audit. The evidence JSON records exact source and actual pinned API hashes.

Mathematical result: **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Proposed formalization credit: **George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA**, with AI assistance and no email. Persson, Meyer and Musco retain the original question's attribution.

## Exact original assertion

Use real matrices indexed by `Fin n`. Retain all `n ≥ 2`, all `1 ≤ k < n`, all real symmetric PSD matrices `Ahat ≤ A`, every admissible function, every allowed eigenbasis choice, and all `epsilon ≥ 0`.

Represent a half-line function by `f : ℝ → ℝ`, with exactly:

- `ContinuousOn f (Set.Ici 0)`;
- `ConcaveOn ℝ (Set.Ici 0) f`;
- `MonotoneOn f (Set.Ici 0)`;
- `∀ x ≥ 0, 0 ≤ f x`.

No assumption `f(0)=0`, global continuity, operator monotonicity or strict monotonicity may be introduced. Arbitrary real extensions are harmless only after proving the actual finite PSD CFC depends solely on the nonnegative half-line.

Use genuine ordered spectral data `d` for a matrix X: `a : Fin n → ℝ`, an actual `Q : Matrix.unitaryGroup (Fin n) ℝ`, `Antitone a`, all `a_i ≥ 0`, and actual reconstruction `X = Q * diagonal a * Q.transpose`. The final assertion quantifies over **every** such data choice, not Mathlib's preferred choice alone. A separate existence theorem prevents vacuity. For any `k` define

`trunc d k = Q * diag(if i.val < k then a_i else 0) * Qᵀ`,

`funcTrunc d f k = Q * diag(if i.val < k then f(a_i) else 0) * Qᵀ`,

and `fc f X = cfc (R := ℝ) f X` using Mathlib's actual matrix functional calculus. Original/function truncations share this **same Q**. In particular `funcTrunc` is neither `f(trunc d k)` nor the full `f(X_k)` when `f(0)>0`, nor an independently rotated truncation inside a newly created plateau of f.

Define the exact canonical squared Frobenius expression

`FSq M = ∑ i, ∑ j, (M i j)^2`.

For real entries this equals the canonical `∑ |M_ij|²`; additionally prove its bridge to the genuine Mathlib Frobenius norm squared. Keep the norm instance local to that bridge, so selecting Frobenius norm does not silently alter the instance used by generic CFC elsewhere.

The intended final proposition is precisely:

```text
∀ n ≥ 2, ∀ k, 1 ≤ k → k < n →
∀ A Ahat : Matrix (Fin n) (Fin n) ℝ,
  A.PosSemidef → Ahat.PosSemidef → Ahat ≤ A →
∀ f : ℝ → ℝ, AdmissibleFunction f →
∀ dA : OrderedSpectralData A,
∀ dHat : OrderedSpectralData Ahat,
∀ epsilon : ℝ, 0 ≤ epsilon →
  FSq A - FSq (trunc dHat k)
    ≤ (1 + epsilon) * FSq (A - trunc dA k) →
  FSq (fc f A - funcTrunc dHat f k)
    ≤ (1 + epsilon) * FSq (fc f A - funcTrunc dA f k).
```

**The premise must remain this difference of squared norms.** The manuscript proves a stronger result under the weaker ordinary residual premise. That result may be an intermediate theorem, but its residual premise must not replace the final canonical statement. No converse equivalence between the two premises is asserted.

## Proposed proof-independent generic contracts

These are precise mathematical contracts for the later statement package, not already compiled Lean signatures. The final package should expose all bridges necessary to make its main assertion auditable; helper grouping can be adjusted before its two independent statement reviews.

1. **Frobenius identity and faithfulness.** For every real matrix M of the stated finite shape, `FSq M = ‖M‖_F² = trace(Mᵀ*M)`, `0 ≤ FSq M`, and `FSq M = 0 ↔ M=0`. The norm equality uses the actual pinned Frobenius norm. For actual orthogonal U,V, `FSq(U*M*V)=FSq M`.

2. **Actual ordered spectral existence/semantics.** Every real PSD X admits ordered data; its selected columns are an orthonormal eigenbasis of the actual X, and its full combination reconstructs X. Include repeated eigenvalues. Reuse the same honest definition as RA-08, but do not import its admitted Challenge. Any future reuse of its implementation must use its reviewed completed source, with attribution and pinned provenance.

3. **Actual finite CFC for arbitrary selected data.** For every d of X and every real function f, `fc f X = Q diag(f∘a) Qᵀ`; if f=g on `[0,∞)`, their CFC values agree for this PSD X. Finite-spectrum continuity justifies the bare-function auxiliary theorem. No supplied spectral formula may be defined to be CFC.

4. **Truncation order and exact tails.** For every d and `k ≤ n`, `trunc d k` is PSD and `trunc d k ≤ X`. For `k<n`,
   `FSq(X-trunc d k)=Σ_{i.val≥k} a_i²` and
   `FSq(fc f X-funcTrunc d f k)=Σ_{i.val≥k} f(a_i)²`.
   These identities hold without a preferred repeated-eigenvalue choice. Also prove `trunc d k=X ↔ ∀ i, k≤i.val → a_i=0`, useful at zero tail.

5. **Trace-deficit reduction.** For real PSD `B≤A`, prove the actual identities and sign
   `FSq(A-B)=FSq A-FSq B-2 trace(B*(A-B))` and `0≤trace(B*(A-B))`; hence `FSq(A-B)≤FSq A-FSq B`.
   For the canonical pair use `B=trunc dHat k≤Ahat≤A`. No commutation of A and B may be assumed.

6. **Scalar consequences of admissibility.** Derive `f(x)/x` antitone on positive x from actual concavity and `f(0)≥0`. For `tau>0`, `c=f(tau)/tau`, derive f(x)≥cx on `0≤x≤tau`, f(x)≤cx above tau, and `0≤f(y)-f(x)≤c(y-x)` when `0≤x≤y` and `tau≤y`. If `f(tau)=0`, prove `∀x≥0, f(x)=0`. These are conclusions from the original function assumptions.

7. **Ordered scalar certificate.** For any original admissible f, `tau>0`, `f(tau)>0`, `c=f(tau)/tau`, `a>0`, `b>0`, set `h(a)=max(c²a²-f(a)²,0)`. Prove exactly

   `h(a)+2 f(b)f(a)-2c²ba-f(b)²+c²b²`
   `≥ f(b)*max(f(b)-cb,0)*(1-b/a)`.

   This is the source's nontrivial scalar lemma, not an assumption in a final matrix theorem. Include all branch endpoints `b=tau`, `z=1`, `z=d`, `d=1`.

8. **Diagonal harmonic constraint from actual PSD order.** For any finite nonnegative vector a, unit vector v (`Σv_i²=1`) and b>0, if the actual matrix `diag(a)-b*(v vᵀ)` is PSD, prove both
   `a_i=0 → v_i=0` and `b * Σ_i (v_i²/a_i) ≤ 1`.
   Real division at zero is used only in this finite formula, with the null-space support condition proved separately. This avoids assuming any Moore–Penrose inverse, inverse square root, range condition or spectral premise.

9. **Actual overlap weights and matrix expansions.** For any selected dA,dHat, define `p_ij=((QAᵀ*QHat)_ij)²`. Prove `p_ij≥0`, `Σ_i p_ij=1`, `Σ_{j.val<k}p_ij≤1`. Write `a_i=dA.a_i`, `b_j=dHat.a_j`, B=trunc dHat k, C=funcTrunc dHat f k. Prove the actual identities

   `FSq(A-B)=Σ_i a_i² + Σ_{j<k}b_j² - 2Σ_{j<k} b_j Σ_i p_ij a_i`,

   `FSq(fc f A-C)=Σ_i f(a_i)² + Σ_{j<k}f(b_j)² - 2Σ_{j<k} f(b_j) Σ_i p_ij f(a_i)`.

   From actual `B≤A`, prove that every selected column with `b_j>0` satisfies the support and harmonic conditions in contract 8. For selected `b_j=0`, retain the value `f(0)` and prove its averaging inequality directly.

10. **Positive-tail excess and tail comparison.** For the entire original ordered pair and every dA,dHat, set `tau=a_k` with zero-based index k, `TA=Σ_{i.val≥k}a_i²`, `Tf=Σ_{i.val≥k}f(a_i)²`. If `tau>0`, prove
    `FSq(fc f A-C)-Tf ≤ c²*(FSq(A-B)-TA)` and `c²*TA≤Tf`.
    The `f(tau)=0` case is part of this theorem, handled separately; it must not become a restriction on the final input class.

11. **Zero-tail closure with f(0) retained.** If `tau=0` and the original trace-deficit premise holds, prove `A=B=Ahat` and both the actual output squared error and the actual optimal-truncation tail equal `(n-k)*f(0)²`. The bases of A and Ahat may differ on the null space. Never use `f(0)/0`, assert the two function truncations are equal, or replace C by the full f(B).

12. **Full canonical affirmative theorem.** Combine the preceding conclusions to prove exactly the universal proposition displayed above. This final theorem has no scalar-certificate, spectral-existence, harmonic, CFC, norm or numerical premise supplied by its caller.

## Computation-minimal route

The required mathematics is finite algebra for arbitrary dimensions, not numerical enumeration. The source's unordered theorem, optimal constant-two example, power-integral argument, stronger function class and sharpness assertions need not be exported to solve RA-09. They were read to verify scope, not proposed as extra implementation work.

For the positive-tail proof, follow the source scalar certificate and average it using actual overlap weights. Avoid introducing CFC of the auxiliary h: its contribution is simply the finite sum `Σ_i h(a_i)p_ij`, already enough for the proof. Likewise, avoid a general projector/Ky Fan variational theorem: row sums of squared entries of the actual orthogonal overlap matrix give `Σ_{j<k}p_ij≤1` directly.

The harmonic constraint has a short direct route. Testing PSD `diag(a)-b vvᵀ` on each coordinate with a_i=0 proves v_i=0. Test it again on the actual vector `z_i=v_i/a_i`. Let `H=Σ_i v_i²/a_i≥0`. The exact quadratic form is `H-bH²≥0`, yielding `bH≤1` by splitting H=0/H>0. Thus there is no need to formalize A+, its range, an inverse square root or an eigenvalue of a rank-one operator. For a canonical column v_j, actual spectral reconstruction proves `b_jv_jv_jᵀ≤B≤A`, and conjugating by QA yields precisely this diagonal premise.

For scalar normalization below tau, put `d=f(b)/(cb)≥1`, `z=a/b>0`. The source's three factorizations can be verified with exact ring/field reasoning and ordered inequalities. Its first quadratic

`Q(d,z)=2(d+1)z²-(2d+1)z+d`

has the explicit sum-of-squares identity

`Q = 2(d-1)(z-1/2)² + (d-1)/2 + 4(z-3/8)² + 7/16`.

This makes positivity immediate for every d≥1 and every real z; no discriminant machinery, quantifier elimination or bounded interval subdivision is needed. The other two branches have manifest nonnegative factors. This proposed identity is exact elementary algebra, not an already kernel-checked certificate.

After summing the averaged certificate, set `D_i=f(a_i)²-c²a_i²`. The terminal bound is `Σ_i max(D_i,0)`. Ordered eigenvalues and the scalar ratio inequalities give D_i≤0 for i<k and D_i≥0 for i≥k, with ties contributing zero. It is therefore exactly `Tf-c²TA`. Padded zero b_j columns are handled through `f(a_i)≥f(0)`, not by dropping their f(0) contribution.

To pass from excess to the relative conclusion, only `c²≥0`, `epsilon≥0`, the residual premise and `c²TA≤Tf` are needed. **No Eckart–Young/best-rank theorem or nonnegativity of the residual excess is required for this implication.** The final canonical quantities are explicit errors of the actual stated truncations; their exact spectral identities suffice. This avoids adding a substantial and unnecessary matrix-optimization foundation.

For the trace-deficit sign, diagonalize B and use nonnegative diagonal entries of the genuine congruence of A-B, then trace cyclicity. A CFC square-root argument is unnecessary. In the zero-tail case, the trace bridge forces A=B; order antisymmetry gives Ahat=A. Exact truncation identities force every discarded Ahat eigenvalue to be zero. The actual CFC/Frobenius tail formula then yields `(n-k)f(0)²` for any permitted null-space basis.

## Actual pinned APIs and missing glue

Inspected Mathlib commit: `0df444a360eaa60ab8c11dca51a86af692955474`; LeanCert commit: `621a43d7cf21f87872392a01e874f2f1dbddc926`; intended toolchain Lean 4.33.1. The ten dependency repositories remain read-only. No build/cache copy/download was run for this note.

| Actual API | Use and remaining obligation |
| --- | --- |
| `Matrix.frobenius_norm_def`, `frobeniusNormedAddCommGroup` in `Analysis/Matrix/Normed.lean:509,550` | Actual norm available. Prove squared finite-sum/trace bridge once; isolate its scope to avoid accidental CFC/norm-instance changes. |
| `Matrix.trace_mul_comm`, `trace_mul_cycle`, `trace_diagonal` in `LinearAlgebra/Matrix/Trace.lean` | Cyclic/diagonal expansions available. New small lemmas must connect these to FSq and the two overlap error identities. |
| `Matrix.PosSemidef.dotProduct_mulVec_nonneg`, `.conjTranspose_mul_mul_same`, `.diag_nonneg`, `.trace_nonneg` in `LinearAlgebra/Matrix/PosDef.lean` | Actual quadratic-form and congruence tools exist. The rank-one domination/harmonic finite-sum helper is new glue, not an API assumed to exist. |
| `Matrix.le_iff`, `nonneg_iff_posSemidef` in `Analysis/Matrix/Order.lean` | Genuine Loewner order is available; use it for truncation order, rank-one subtraction and zero-tail antisymmetry. |
| `Matrix.IsHermitian.eigenvalues₀_antitone`, `.spectral_theorem`, `.mulVec_eigenvectorBasis`; `Matrix.PosSemidef.eigenvalues_nonneg` | Sorted spectral existence is available. Be careful: general-index `.eigenvalues` reindexes by an arbitrary equivalence; sorted `Fin n` semantics require the actual ordering bridge. |
| `Matrix.IsHermitian.cfc_eq`, finite real spectrum in `Analysis/Matrix/HermitianFunctionalCalculus.lean` and `Spectrum.lean` | Genuine bare-function finite CFC exists. Equality with every caller-supplied ordered eigenbasis remains a required generic bridge, shared in mathematical content with RA-08. |
| `OrthonormalBasis.sum_sq_inner_right/left` in `Analysis/InnerProductSpace/PiL2.lean:530,537` | Parseval is available; direct matrix orthogonality may be shorter for overlap column sums and restricted row sums. No claim of an existing specialized Frobenius orthogonal-invariance lemma. |
| `ConcaveOn` and `concaveOn_iff_div` in `Analysis/Convex/Function.lean:57,1016` | Actual concavity permits the ratio lemma. The piecewise ordered scalar certificate itself still needs implementation. |

I found no single existing theorem that already closes the complete ordered scalar/weighted transfer argument. The genuine missing glue is manageable and explicit above. The feasibility does not depend on importing a mathematical result as an axiom or assuming a desired matrix inequality.

LeanCert should be used truthfully for kernel trust assertions and dependency checks on the final exports. This proof is pure exact universal algebra and finite spectral analysis; no numerical box is needed. Do not add a decorative unused singleton merely to advertise interval use. If the shared campaign guide requires a material numerical certificate, discuss the pure-algebra scope before freezing the statement package, as for RA-07; do not narrow unbounded scalar variables to a finite box. Expected final axiom dependencies are only the standard three or subsets. Actual dependency traversal, independent final reviews, Linux Comparator and default-kernel replay remain mandatory.

## Next authorized stage

This note is ready to guide an isolated RA-09 statement-only project once the coordinator allocates that task. Write Definitions/Challenge/NUMERICAL_TARGETS/source mapping, expose every listed bridge, freshly typecheck and inspect actual instances, then obtain two independent hash-bound statement approvals before implementation. Do not describe RA-09 as Lean verified until its complete proof and actual operational gates pass.
