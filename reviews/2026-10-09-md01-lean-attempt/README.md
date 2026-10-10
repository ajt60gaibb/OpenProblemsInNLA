# MD-01 Lean attempt — updated 10 October 2026

This is an experimental, **partial** Lean formalization associated with the
[MD-01 proof audit](../2026-10-08-claimed-solutions/MD-01.md). It does not
prove the original conjecture or certify the paper. The canonical MD-01 status
remains **Solution claimed**, not **Lean verified**.

## Checked scope

| File(s) | Kernel-checked result | Remaining premise or limit |
| --- | --- | --- |
| `Target.lean` | Defines the exact trace-normalized SDP and original expectation limit. For positive order, proves feasibility, boundedness, integrability, compactness, maximum attainment, and equivalence of `sSup` to the canonical maximum. | Declaring `sharpThetaExpectation : Prop` does not prove it. |
| `DualWitness.lean`, `Bridge.lean` | Prove PSD trace-pairing nonnegativity, weak duality, and the paper's rescaled target-matrix upper bound for the exact MD-01 theta value. | Existence and PSD of the random target matrix with the required coefficient are hypotheses. |
| `Complement.lean` | From the same PSD target matrix for a fixed graph `G`, explicitly constructs a feasible SDP matrix for `Gᶜ` and proves `theta(Gᶜ) ≥ n/(1+1/a)`. | This is a pointwise complement bound conditional on the witness. Passing to `theta(G)` uses symmetry of the random-graph law. |
| `GraphLower.lean`, `ThetaLower.lean` | Prove exact singleton mass and complement expectation symmetry for mathlib's `G(n,1/2)` measure, then the exact expectation lower bound from the explicit premise `n ≤ theta(G) theta(Gᶜ)` for every graph. | The deterministic theta complement-product inequality is not proved here. The paper's explicit witness offers a separate route to asymptotic lower bounds. |
| `VaryingUpper.lean`, `ThetaUpper.lean` | On probability spaces varying with `n`, a uniform `L²` bound plus convergence in probability gives convergence of expectations. The graph-specific theorem derives the exact `sharpThetaExpectation` proposition from those two explicit hypotheses. | The uniform `L²` estimate and the paper's convergence-in-probability theorem are not proved. |
| `ExpectationBridge.lean` | Earlier fixed-space version of the `L²` expectation transfer. | Superseded for the varying graph spaces by `VaryingUpper.lean` and `ThetaUpper.lean`. |
| `MomentWitness.lean` | Proves that every term in the identified four-label sign product is one, its injective sum is `(n)_4`, and the corrected slack-exponent arithmetic, including the even-degree `O(1)` case. | The file alone does not identify the product with a graph-matrix mixed trace or prove the general corrected Theorem 3.24. |
| `UniformSigns.lean`, `GraphBits.lean`, `GraphMeasureParity.lean` | Encode graph edges as Boolean bits and prove the exact even-edge parity rule for signed monomials under the actual `G(n,1/2)` measure. | No graph-shape intersection count follows from parity alone. |
| `GraphMatrix.lean`, `GraphShapeMoment.lean`, `ConcreteWitness.lean`, `ConcreteTrace.lean` | Define injective-labeling graph matrices, expand the full four-block trace, transfer weights to graph-edge monomials, and prove the expected raw mixed trace is at least `(n)_4` for the four concrete shapes. | The `Shape` type covers proper singleton-boundary simple-edge cases, not every multigraph shape in the paper. Matrices are unnormalized; the corrected general Theorem 3.24 and spectral estimates remain open. |

The formal target uses `SimpleGraph.binomialRandom (Fin n)` at probability
`1/2`. Its matrix constraints and objective match the retained trace-one SDP;
for `n > 0`, `Target.lean` proves that the encoded supremum is actually the
original maximum. The `n = 0` convention cannot affect an `atTop` limit.

Coauthor Aaron Potechin confirmed to the maintainer on 10 October 2026 that
the general Theorem 3.24 remainder should be `O(sqrt n)` while the equal-shape
special case retains `O(1)`. He also confirmed that Definition 4.3's
"appears earlier" clause must exclude the starting boundary vertex `u`, not
`v`. The [mathematical audit](../2026-10-08-claimed-solutions/MD-01.md) gives
an exact counterexample to each printed statement and the parity argument
for the `O(sqrt n)` repair. The corrected paper has not yet been posted.

## Reproduction and trust scope

The sources were checked on macOS with Lean 4.33.1 and mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`. `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json` pin the dependency set. From this
directory in a prepared Lean installation, first fetch the pinned cache with
`lake exe cache get`. Compile each file with `lake env lean File.lean`; for
files imported by another local file, first write its module with
`lake env lean -o File.olean File.lean` and include this directory in
`LEAN_PATH`. The checked dependency order is:

```text
Target, DualWitness, GraphLower, VaryingUpper,
UniformSigns, GraphBits, GraphMatrix,
Bridge, Complement, ThetaLower, ThetaUpper,
ExpectationBridge, MomentWitness,
GraphMeasureParity, GraphShapeMoment, ConcreteWitness, ConcreteTrace
```

The local run used an already built mathlib cache at the pinned revision.
Every checked file compiled with exit code zero and no `sorry`, `admit`, or
custom axiom declarations. `#print axioms` reports only subsets of
`propext`, `Classical.choice`, and `Quot.sound` for proved theorems. These
local checks are not the catalog's independent statement reviews, fresh
Linux build, or Lean Comparator check. In particular, no unconditional MD-01
limit theorem has a proof body.

## Remaining work before any Lean verification claim

1. Independently review the formal target statement and proof interface
   against the canonical MD-01 problem.
2. Formalize and prove the corrected paper's graph-matrix intersection and
   block-walk estimates, including the Section 4 definition correction, and
   the spectral, truncation, and PSD-witness construction with the required
   high-probability bounds.
3. Prove the uniform `L²` estimate for the normalized theta sequence (or an
   equivalent uniform-integrability theorem) and discharge the explicit
   convergence-in-probability hypothesis in `ThetaUpper.lean`.
4. Prove the unconditional `sharpThetaExpectation` declaration and run the
   catalog's full project, referee, Comparator, axiom, and fresh Linux checks.

The partial formal results do not warrant changing MD-01 to `Solved` or
`Lean verified`.
