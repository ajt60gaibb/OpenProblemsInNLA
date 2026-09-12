# MI-06 Lean formalization: local proof complete

This package formalizes Matthew J. Colbrook's fixed
rational counterexample to the [original MI-06 conjecture](../README.md).
The [complete informal source](../solution.tex) also proves a stronger
no-finite-constant result; the Lean target is the full negation of the original
universal assertion with factor `√2`.

**Status:** both independent statement reviews approved the frozen boundary;
the complete local proof build passed. Two independent final proof reviews and
authoritative Linux verification are pending. The six intentional `sorry`
placeholders occur only in the statement-only [Challenge](Challenge.lean), which
the completed [proof](NLA/MI06/Proof.lean) and [six public exports](Solution.lean)
never import. All 52 source declarations passed kernel trust assertions with
only `propext`, `Classical.choice`, and `Quot.sound`. This is local macOS build
evidence; the package does not yet claim the repository's Lean-verified status.

Formalization author: **George Stepaniants**, Department of Computing and
Mathematical Sciences, California Institute of Technology, Pasadena,
California, USA. Mathematical counterexample: **Matthew J. Colbrook**,
Department of Applied Mathematics and Theoretical Physics, University of
Cambridge. AI assistance and independent-agent reviews will be documented
separately; neither is external human peer review.

[Definitions](NLA/MI06/Definitions.lean) retain the actual CFC matrix modulus,
the arithmetic average of left and right moduli, genuine complex unitaries,
and ordinary Hermitian PSD order. [Numerical and semantic targets](NUMERICAL_TARGETS.md)
were frozen before proof work and remain unchanged. A nonzero vector in a
two-constraint kernel avoids eigenvalue computations and unit-vector
normalization. The explicit-kernel LeanCert certificate is the exact point
inequality `2 < 9/4`; [proof-term inspection](reviews/proof-inspection.log)
confirms it is retained in the final conjecture negation.

The package pins Lean `v4.33.1`, LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`; all ten dependency commits are
recorded in [the Lake manifest](lake-manifest.json). To build the complete proof:

```
lake build Solution
```

[Comparator configuration](comparator.json) declares the six exports
and the permitted standard axioms `propext`, `Classical.choice`, and
`Quot.sound`. Actual Comparator checking and kernel replay require the repository's
[Linux verification workflow](../../../docs/lean/README.md); they have not been
run for this package. The completed-project `formalization.yaml` will be added
during publication preparation against the repository's pinned schema.

[Statement approvals](reviews/statement-freeze.json),
[proof completion and scope](reviews/proof-completion.md), and
[final source hashes](reviews/proof-freeze.json) record the review boundary.
