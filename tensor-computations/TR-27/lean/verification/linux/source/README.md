# TR-27: complete projective tensor-square counterexample

All 25 independently reviewed mathematical statements have complete Lean proofs. **Authoritative verification and final independent approval are pending; the canonical status remains Solved.** Local proof elaboration and transitive axiom audits pass with only `propext`, `Classical.choice`, and `Quot.sound`.

The result refutes the [complete original problem](../README.md). It constructs a reduced irreducible nondegenerate complex projective curve and a point with rank 3, border rank at most 2, and rank 9 at the ordinary, unmerged Segre tensor square. All decomposition coefficients and variable parameters range over arbitrary complex numbers; lower bounds cover the whole variety, repetitions, zero summands, infinity and separately chosen left and right tensor factors.

Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. Original mathematical counterexample and proof: **Matthew J. Colbrook**; see the [complete source manuscript](../../../references/colbrook-tensor-metrics-rank-2026-09-11/manuscripts/tr27_solution.tex). Original conjecture authorship and the existing author feedback remain on the canonical page. No contact email is added. Substantial AI assistance and review roles are disclosed in [formalization.yaml](formalization.yaml); the independent agent reviews adapt the [repository's Tau Ceti referee protocol](../../../docs/lean/REVIEW.md) and are not human peer review or official Tau Ceti endorsement.

## Mathematical boundary and proof

[Challenge.lean](Challenge.lean), [Definitions.lean](NLA/TR27/Definitions.lean), [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md), and [comparator.json](comparator.json) retain the exact bytes approved by two independent agents **before proof implementation**. Their [statement freeze](reviews/statement-freeze.json) is a historical receipt. Draft, unreviewed, pending and no-complete-verification wording inside those frozen documents or development-module headers describes their creation stage, not this package's current status; current status is stated above and in the metadata. The Challenge's 25 deliberate placeholders exist only in the trusted reference environment. Solution imports no Challenge and contains no unresolved proof.

[Counterexample.lean](NLA/TR27/Counterexample.lean) proves the full original universal implication false. The proof chain includes:

- Generic projective/cone rank, genuine rank minima, affine/projective all-polynomial Zariski closure, independent-factor Segre rank and coordinate invariance.
- An exact quotient of the degree-12 rational normal curve. Integrality, lying over and the complex Nullstellensatz prove equality of the entire algebraic zero locus with the exhaustive parameter cone.
- Actual closedness, irreducibility, reducedness and full span; uniform independence for any eight distinct points of the whole curve.
- A three-term vector of rank exactly 3, a polynomial border-rank-two degeneration, and exclusion of every at-most-eight-term tensor-square decomposition by separate dual-coordinate supports.

The two final declarations conclude without assuming any missing geometry, independence, rank inequality or source lemma. Standard Mathlib facts are kernel checked; the informal source is not imported as an axiom. Exact algebra avoids artificial numerical certificates. LeanCert is used for explicit kernel-trust assertions on **every selected declaration** in [Solution.lean](Solution.lean). Optional source strengthenings—smoothness, exact border rank 2, arbitrary prescribed longer delays and eventual saving—are not claimed and are unnecessary for the complete negative answer.

## Reproduction and review

Pins: Lean 4.33.1, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Comparator and its sandbox/control sources are locked by [the shared verifier](../../../tools/lean/source-lock.json).

From the repository root on the supported non-root Linux environment, follow the [shared setup](../../../docs/lean/README.md), then run:

```sh
tools/lean/bootstrap.sh /absolute/path/to/verification-tools
tools/lean/verify.sh tensor-computations/TR-27/lean /absolute/path/to/verification-tools
```

The real verifier tests its sandbox and rejection controls, materializes tracked immutable inputs and pinned dependencies into a fresh directory, builds the separate Challenge and Solution environments, checks all 25 statements with no definition holes, and replays the proofs in the default Lean kernel using only the three permitted axioms. A successful local `lake build` alone does not replace those gates.

Historical local author evidence and independent module reviews are retained under [reviews](reviews/). [The complete local build log](reviews/complete-local-development.log) records all proof modules. It uses cached dependencies and makes no Linux verification claim. The frozen historical specification's external source-audit link is preserved through [the source-assessment pointer](../target-review.md); [API reconnaissance](specification/api-reconnaissance.md) and [source-target design](specification/source-target-design.md) are also retained.
