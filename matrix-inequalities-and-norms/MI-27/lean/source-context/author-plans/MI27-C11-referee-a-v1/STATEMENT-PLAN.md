# MI27 C11 continuation: identity-shift boundary and FTC

Author: Codex agent `/root/nr04_mf14_final_referee_a`, contributing for George
Stepaniants, Department of Computing and Mathematical Sciences, California
Institute of Technology. This makes this agent a MI27 source author; its prior
NR04 and MF14 reviews remain reviews of other authors' work.

These exact helper statements are recorded before their proof bodies. They
extend the already compiled `NLA.MI27.IdentityShift`; they do not replace or
weaken frozen C11. No Lean process is run by this author. Root alone compiles
serially with one thread and a 4096 MiB limit.

The frozen C11 Challenge SHA-256 is
`1cacb3aa3088860016b9d121904677d56c6c8e6025de9eeaf262957c2bc0d640`.
It requires the ordinary noncommuting Umegaki expression to equal the finite
two-sided hockey-stick integral for every strict density pair and every valid
R >= 1. C12 is downstream, not a possible premise for proving C11.

Prior attempts inspected: the retained MI27-agent-C11 statement plan,
IdentityShift and FiniteHockeyStick source/handoff, and the retained route
review. Their solved scope is finite integrability/cutoffs and the actual
fixed-eigenbasis shift expansion/derivative. Their remaining interfaces include
complex-Hermitian congruence inertia, measurable layer cake/Tonelli, scalar
pencil integrals, trace-log/determinant compatibility, the identity-shift
boundary at infinity/FTC, and substitutions. This task removes the boundary
and finite-FTC portion without assuming any of the remaining interfaces.

## Exact first module headers: IdentityShiftLimit.lean

All declarations are in namespace `NLA.MI27` with the existing matrix/norm
scopes. `Filter` and `Topology` notation use their ordinary Mathlib meanings.

```lean
lemma c11_scalar_shift_error_bounds (x y r : ℝ)
    (hx : 0 < x + r) (hy : 0 < y + r) :
    0 ≤ (x + r) * (Real.log (x + r) - Real.log (y + r)) - (x - y) ∧
      (x + r) * (Real.log (x + r) - Real.log (y + r)) - (x - y) ≤
        (x - y) ^ 2 / (y + r)

lemma c11_tendsto_scalar_shift (x y : ℝ) :
    Filter.Tendsto
      (fun r : ℝ => (x + r) * (Real.log (x + r) - Real.log (y + r)))
      Filter.atTop (nhds (x - y))

lemma c11_overlap_trace_difference {n : ℕ} (hn : 1 ≤ n) (X Y : Mat n)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (∑ i : Fin n, ∑ j : Fin n,
      (hX.eigenvalues i - hY.eigenvalues j) *
        NLA.MI24.unitaryOverlapWeight
          (star hX.eigenvectorUnitary * hY.eigenvectorUnitary) i j) =
      trR (X - Y)

lemma c11_tendsto_relative_entropy_identityShift {n : ℕ} (hn : 1 ≤ n)
    (X Y : Mat n) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    Filter.Tendsto
      (fun r : ℝ => relEntropy (c11_identityShift X r) (c11_identityShift Y r))
      Filter.atTop (nhds (trR (X - Y)))

lemma c11_tendsto_density_relative_entropy_identityShift {n : ℕ} (hn : 1 ≤ n)
    (ρ σ : Mat n) (hρ : StrictDensity ρ) (hσ : StrictDensity σ) :
    Filter.Tendsto
      (fun r : ℝ => relEntropy (c11_identityShift ρ r) (c11_identityShift σ r))
      Filter.atTop (nhds 0)
```

The stronger Hermitian scope of the fourth header is intentional: sufficiently
large identity shifts have positive scalar logarithm arguments, regardless of
the original eigenvalues. No simultaneous diagonalization is used. The exact
scalar bound follows from log(u) <= u-1 twice and gives an O(1/r) remainder;
both unitary-overlap marginals then give the literal trace difference.

## Proposed second module interface: IdentityShiftFTC.lean

This definition is an explicit finite scalar expression, not an entropy or
integral identity hidden in a definition:

```lean
def c11_shiftKernel {n : ℕ} (X Y : Mat n)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (r : ℝ) : ℝ :=
  -(∑ i : Fin n, ∑ j : Fin n,
    (Real.log (hX.eigenvalues i + r) - Real.log (hY.eigenvalues j + r) +
      (hY.eigenvalues j - hX.eigenvalues i) / (hY.eigenvalues j + r)) *
        NLA.MI24.unitaryOverlapWeight
          (star hX.eigenvectorUnitary * hY.eigenvectorUnitary) i j)

lemma c11_shiftKernel_continuousOn {n : ℕ} (X Y : Mat n)
    (hX : X.PosDef) (hY : Y.PosDef) :
    ContinuousOn (c11_shiftKernel X Y hX.isHermitian hY.isHermitian) (Set.Ici 0)

lemma c11_shiftKernel_finite_integral {n : ℕ} (hn : 1 ≤ n) (X Y : Mat n)
    (hX : X.PosDef) (hY : Y.PosDef) (R : ℝ) (hR : 0 ≤ R) :
    IntervalIntegrable (c11_shiftKernel X Y hX.isHermitian hY.isHermitian)
      MeasureTheory.volume 0 R ∧
      (∫ r in (0 : ℝ)..R, c11_shiftKernel X Y hX.isHermitian hY.isHermitian r) =
        relEntropy X Y - relEntropy (c11_identityShift X R) (c11_identityShift Y R)

lemma c11_tendsto_shiftKernel_integral {n : ℕ} (hn : 1 ≤ n) (ρ σ : Mat n)
    (hρ : StrictDensity ρ) (hσ : StrictDensity σ) :
    Filter.Tendsto
      (fun R : ℝ => ∫ r in (0 : ℝ)..R,
        c11_shiftKernel ρ σ hρ.1.isHermitian hσ.1.isHermitian r)
      Filter.atTop (nhds (relEntropy ρ σ))
```

This last header is a limit of actual finite interval integrals. It does not
yet assert a Bochner integral over an unbounded interval or the required
positive-part/layer-cake identity. Full C11 remains incomplete until those
separate connections are proved and compiled.
