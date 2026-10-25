# IE-22 lower construction: pinned finite-sampling API route

Read-only API research by `/root/inventory`, 2026-10-23. Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`, Lean 4.33.1. The declarations below
were read in the actual pinned sources; no IE-22 proof or new statement source
was implemented, and no complete proof skeleton is claimed compiled.

**Use finite-product variance directly, then extract a point outside a bad
union.** No strong law, infinite sample, Hoeffding theorem, sphere-law identity
or measurable-good-event argument is necessary for this existence endpoint.

## Finite test-family sampling

Fix any probability space `(Ω,μ)`, finite test index J, measurable real tests
`f_j` with values in `[0,T]`, tolerance `δ>0`, and a requested row-count lower
bound `M0`. For each chosen positive natural m use the actual sample law

```
P_m = Measure.pi (fun _ : Fin m => μ)
avg_j(ω) = (1 / (m : ℝ)) * sum_i f_j(ω i).
```

The following pinned APIs provide the complete elementary route:

| Declaration | Exact role / source |
|---|---|
| `MeasureTheory.memLp_of_bounded h hf 2` | From `h : ∀ᵐ ω ∂μ, f ω ∈ Set.Icc a b` and `hf : AEStronglyMeasurable f μ`, obtains `MemLp f 2 μ`. `MeasureTheory/Function/LpSeminorm/Basic.lean:553`. `MemLp.of_bound hf C hnorm` is the norm-bound variant at line 549. |
| `MeasureTheory.MemLp.integrable hq1 hf` | With `hq1 : 1≤q`, finite μ and `hf : MemLp f q μ`, obtains integrability. The order of explicit arguments starts with `hq1`. `MeasureTheory/Function/L1Space/Integrable.lean:659`. |
| `MeasureTheory.measurePreserving_eval μ i` | Actual coordinate projection from `Measure.pi μ` to marginal `μ i`; `.map_eq` and `MemLp.comp_measurePreserving` transport each coordinate test. `MeasureTheory/Constructions/Pi.lean:402`. |
| `MeasureTheory.integral_comp_eval hf` | For finite product probability measures, `∫ ω, f(ω i) ∂Measure.pi μ = ∫ x, f x ∂μ i`, assuming only marginal AE strong measurability. `MeasureTheory/Integral/Pi.lean:144`. |
| `ProbabilityTheory.variance_sum_pi h` | Directly gives `Var[∑ i, (fun ω => X i (ω i)); Measure.pi μ] = ∑ i, Var[X i; μ i]`, for any finite index, probability marginals and `h : ∀ i, MemLp (X i) 2 (μ i)`. This avoids separately rebuilding pairwise independence. `Probability/Moments/Variance.lean:447`. |
| `ProbabilityTheory.variance_const_mul c X μ` | Gives variance of `fun ω => c*X ω` equal to `c²*Var[X;μ]`, with no extra hypothesis. `Probability/Moments/Variance.lean:205`. |
| `ProbabilityTheory.variance_le_sq_of_bounded h hf` | For a probability measure and `h : ∀ᵐ ω, X ω∈Icc a b`, `hf : AEMeasurable X μ`, gives `Var[X;μ]≤((b-a)/2)²`. `Probability/Moments/Variance.lean:499`. |
| `ProbabilityTheory.meas_ge_le_variance_div_sq hX hδ` | With `hX : MemLp X 2 P` and `hδ : 0<δ`, bounds `P {ω | δ≤abs(X ω-∫X)} ≤ ENNReal.ofReal (Var[X;P]/δ²)`. `Probability/Moments/Variance.lean:397`. |
| `MeasureTheory.measure_iUnion_fintype_le P bad` | Gives `P (⋃ j, bad j)≤∑j,P(bad j)` for any finite J, without a measurable-set premise. Finset version: `measure_biUnion_finset_le`. `MeasureTheory/OuterMeasure/Basic.lean:80,84`. |

`Measure.pi` has its probability instance automatically when all marginals
are probability measures (`Constructions/Pi.lean:310`). For fixed j apply
`variance_sum_pi` to `X i = f_j`, then `variance_const_mul` to the reciprocal
sample count. For `m>0` this gives

```
E_Pm avg_j = E_μ f_j,
Var_Pm avg_j = Var_μ f_j / m ≤ T²/(4*m).
```

Use `integral_finsetSum` (current spelling, Bochner/Basic.lean:246) and
`integral_const_mul` (line 288) for the expectation; the old
`integral_finset_sum` spelling is deprecated in this pin. `variance_sum_pi`
uses a finite **sum of functions**; pointwise lambda notation may need a
`change`/function extensionality before rewriting. `simp` handles
`Fintype.card (Fin m)=m`. The L² property of the average comes from the finite
sum and constant multiplication, or directly from its bounded range.

Let `bad j = {ω | δ≤abs(avg_j ω-E_μ f_j)}`. Chebyshev and finite subadditivity
give

```
P_m (union_j bad j) ≤ ofReal (#J*T²/(4*m*δ²)).
```

For ENNReal bookkeeping use `ENNReal.ofReal_sum_of_nonneg`
(`Data/ENNReal/BigOperators.lean:123`) and `ENNReal.ofReal_lt_one`
(`Data/ENNReal/Real.lean:203`). Every variance bound is nonnegative. One can
also use the weaker `T²/m` bound to simplify constants. Choose a natural m
larger than `M0`, zero and the fixed real union-bound coefficient using
`exists_nat_gt`; only elementary positive-denominator algebra remains. There
is no need to establish a filter limit or a uniform-in-n sample complexity.
The finite net is fixed before this choice, so its possibly huge cardinality
is an ordinary finite constant.

### Extracting an actual sample

From `P_m badUnion < 1` and `measure_univ=1`, conclude
`badUnion ≠ Set.univ`; otherwise substitution contradicts the strict bound.
Then apply

```
Set.ne_univ_iff_exists_notMem badUnion
```

(`Data/Set/Basic.lean:572`). A point outside the union has **strict** error
`abs(avg_j-E f_j)<δ` for all j. This route does not require measurability of
the union or positivity of a separately defined good event, and works with
the outer-measure Chebyshev bounds even when only AE measurability is known.

If a positive-good-event statement is desired, with measurable badUnion use
`measure_compl` (`Measure/MeasureSpace.lean:338`), then
`MeasureTheory.nonempty_of_measure_ne_zero` (`Measure/MeasureSpaceDef.lean:189`).
For this finite-matrix witness the outside-union route has fewer obligations.

## Finite-cover extension on the actual Euclidean sphere

Work in `E = EuclideanSpace ℝ (Fin n)` and `S = Metric.sphere (0:E) 1`.
The ordinary function space `Fin n→ℝ` has a different default norm; transport
coordinates using `WithLp.ofLp` when forming the final real matrix.

- `isCompact_sphere (0:E) 1` is available in the proper finite-dimensional
  Euclidean space (`Topology/MetricSpace/ProperSpace.lean:47`).
- `(isCompact_sphere (0:E) 1).finite_cover_balls hη` yields a finite set of
  centers **inside S**, covering S by open balls of positive radius η. Exact
  statement: `∃ t⊆S, t.Finite ∧ S⊆⋃x∈t, Metric.ball x η`
  (`Topology/MetricSpace/Pseudo/Basic.lean:263`, alias at line 270).
- Convert the finite center set to `ht.toFinset`, or use its subtype with
  the `Fintype` supplied by `ht.fintype`. No packing/cardinality estimate is
  needed. The tests for that finite J are the bounded hinge functions.

For an actual unit row u define `φ_x(u)=max(a²-n*inner(u,x)²,0)`. On the
unit sphere, finite Cauchy–Schwarz and difference of squares give
`abs(φ_x(u)-φ_y(u))≤2*n*dist x y`. The empirical average therefore has the same
Lipschitz bound. Its expectation also has that bound: rewrite its difference
using `integral_sub` with integrability, then use
`norm_integral_le_of_norm_le_const` (`Integral/Bochner/Basic.lean:966`), whose
right side is the constant times `μ.real univ=1`. Thus the **centered empirical
error** has Lipschitz constant `4*n`. A finite-net error ≤δ extends to error
≤δ+4*n*η on every genuine unit direction. Choose η after fixed positive n
and the desired extension error. This is the correct safe `4*n` bound.

The row map may be normalized Gaussian with a fixed unit fallback at zero.
Its pointwise unit-row proof makes the preceding bound valid at every sample,
including the zero outcome. The fallback map's measurability must be proved;
normalization is continuous away from zero and singleton zero is measurable.

## Mapping the one-row expectation

For a law representation `hX : ProbabilityTheory.HasLaw X ν μ`, prefer

```
hX.integral_comp hf
```

where `hf : AEStronglyMeasurable f ν`. It gives
`∫ω, f(X ω) ∂μ = ∫x, f x ∂ν` (`Probability/HasLaw.lean:146`). For a genuine
unit linear functional of the actual Gaussian vector, ν is `gaussianReal 0 1`.
This directly transports the bounded hinge expectation to the scalar law.

The underlying general API is `MeasureTheory.integral_map hX hf`
(`Integral/Bochner/Basic.lean:1043`), where `hX : AEMeasurable X μ` and
`hf : AEStronglyMeasurable f (Measure.map X μ)`; its orientation is
`∫y,f y ∂map X μ = ∫ω,f(X ω) ∂μ`. A known map equality rewrites ν first.
For coordinate tests under `Measure.pi`, `integral_comp_eval` already supplies
the required identity without manual map rewrites.

No independence between the finite family of different-direction tests at a
single row is needed. Independence is only across rows, separately for each
fixed test; union bounds combine the different test events. If independence
must be exposed explicitly, `ProbabilityTheory.iIndepFun_pi` takes
`∀i,AEMeasurable (X i) (μ i)` and gives independence of `fun i ω=>X i(ω i)`
(`Probability/Independence/Basic.lean:891`). `variance_sum_pi` already uses this
internally.

For IE-22, take `M0` large enough for `R*n≤m`, positive m and the floor loss
`a²/m` to be small. Apply the finite-sampling result after n and the net have
been fixed. The resulting sample is the desired actual finite matrix; its
all-direction hinge inequality feeds the deterministic trimming dual. This
does not prove the separate quantitative IE-21 probability theorem.
