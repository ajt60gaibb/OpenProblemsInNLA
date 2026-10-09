# MD-01 Lean attempt — 9 October 2026

This is an experimental, **partial** Lean formalization associated with the
[MD-01 proof audit](../2026-10-08-claimed-solutions/MD-01.md). It does not
prove the original conjecture or certify the paper. The canonical MD-01 status
remains **Solution claimed**, not **Lean verified**.

## Checked scope

| File | Kernel-checked declarations | Limit |
| --- | --- | --- |
| `Target.lean` | The original expectation-limit proposition typechecks; the trace-normalized SDP feasible set is nonempty for positive `n`, its objective is bounded above by `n`, and the random variable is integrable. | Typechecking a proposition does not prove it. The file does not prove maximum attainment or the asymptotic limit. |
| `MomentWitness.lean` | Under symmetric sign variables with squares equal to one, the explicit four-label product equals one; its injective sum is `(n)_4`. A squared natural-number inequality implies that `(n)_4/n^(7/2)` is unbounded. It also proves the corrected slack-exponent identity and bounds from the numerical relation in Corollary 3.10. | The file does not define the real quotient, the paper's graph matrices, or the identification of this product with a mixed trace term. The general corrected Theorem 3.24 is not proved. |
| `ExpectationBridge.lean` | On a fixed probability space, a uniform `L²` bound plus convergence in measure to one implies convergence of expectations to one. | The paper's bound, the MD-01 uniform moment estimate, and a coupling of the changing graph spaces are not instantiated. |

The formal statement in `Target.lean` uses mathlib's independent-edge
`SimpleGraph.binomialRandom (Fin n)` measure at probability `1/2`, with
real positive-semidefinite matrices, trace one, edge-zero constraints, and
objective `∑ i, ∑ j, X i j`. It uses `sSup` for the SDP value. Feasibility and
boundedness are proved; equivalence to the published `max` still requires an
attainment proof.
The `n = 0` convention cannot affect an `atTop` limit.

The formal sign-product witness bears on the printed general `O(1)` remainder
in Theorem 3.24; the [mathematical audit](../2026-10-08-claimed-solutions/MD-01.md)
records the shape-to-product identification and the proposed `O(sqrt n)`
repair. The Lean file verifies only the algebra and counting under its stated
premises. The paper's corrected Corollary 1.3 and Claim 4.15, the Section 4
block classification, and the main random-matrix estimates are not formalized.

## Reproduction and trust scope

The sources were checked on macOS with Lean 4.33.1 and mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`. `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json` pin the checked dependency set.
In a prepared Lean installation, from this directory run:

```sh
lake exe cache get
lake env lean Target.lean
lake env lean MomentWitness.lean
lake env lean ExpectationBridge.lean
```

The local run used an already built mathlib cache at the same pinned revision.
Each file compiled with exit code zero and no `sorry`, `admit`, or custom axiom
declarations. `#print axioms` reports only subsets of `propext`,
`Classical.choice`, and `Quot.sound` for its proved theorems. These local
checks are not the catalog's independent statement review, fresh Linux build,
or Lean Comparator check; no MD-01 target theorem has a proof body to check.

## Remaining work before any Lean verification claim

1. Prove that the Lean SDP supremum is attained as the original maximum, and review
   the statement boundary independently against the canonical MD-01 target.
2. Formalize and prove the corrected paper's graph-matrix, intersection,
   block-walk, spectral, and PSD-witness arguments, including the Section 4
   definition correction and all quantitative estimates.
3. Formalize the uniform moment bound and expectation lower bound, and connect
   convergence in probability to the original expectation limit on the graph
   sequence.
4. Prove the final `sharpThetaExpectation` declaration and run the catalog's
   full project, referee, Comparator, axiom, and fresh Linux checks.

The partial checks above support sending the identified corrections to the
authors. They do not warrant changing MD-01 to `Solved` or `Lean verified`.
