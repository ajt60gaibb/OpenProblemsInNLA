# IE-22: complete kernel-verified optimal row-deletion constant

The complete canonical IE-22 target is Lean verified. All 20 independently reviewed required declarations passed the actual non-root Linux Comparator, authentic LeanCert kernel-trust assertions and default-kernel replay. Their transitive axiom closures contain only `propext`, `Classical.choice` and `Quot.sound`.

The proof covers the genuine supremum over every real unit-row matrix, the exact floor-row deletion minimum, the canonical Gaussian integral, the finite projected-Gaussian bound, an explicit squared error rate uniform over every positive row count, deterministic near-extremizers and the limit along every high-aspect sequence, and failure of the original eventual-uniform property for every smaller constant. Rank deficiency, projected zero rows and empty retained selections are included. The exact schedule yields `C = 22 + 4 L² + 8 L`, with `L = 2/(1-theta)`. No floating-point quadrature, numerical eigenvalue search or finite sampling is a proof premise.

Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. Original mathematical proof: **Matthew J. Colbrook**. The canonical statement, original attribution and dated manuscript remain preserved. Substantial AI assistance and every author/reviewer role are disclosed in [formalization.yaml](formalization.yaml); no human peer review or official Tau Ceti endorsement is claimed.

The [20-statement boundary](Challenge.lean) was reviewed independently before implementation. Definitions, Challenge, NUMERICAL_TARGETS and comparator.json remain byte-identical to [their preproof freeze](reviews/statement-freeze.json). Their original draft wording is historical. Challenge's 20 deliberate placeholders specify reference types and are never imported by proof modules. Solution explicitly chooses authentic LeanCert kernel trust and checks every selected declaration.

The sharp Gaussian variance estimate is proved by an exact scalar crossing-kernel identity, absolutely continuous hinge fibers and finite-product variance tensorization. This replaces the manuscript's Hermite-series sketch without assuming its analytic conclusion or changing its constant. The 31 IE-21 mathematical sources are [vendored byte-identically](reviews/IE21-DEPENDENCY.json) from verified revision `1eb284b84ecc0d3c958d022b3e020be7fa111391`; all are freshly rebuilt in this project. There is no mutable local-path or imported compiled-project dependency.

The complete source was independently approved by the [fidelity referee](reviews/ie22-final-fidelity-evidence/source-review.md) and [correctness referee](reviews/ie22-final-correctness-evidence/source-review.md), each a nonauthor of this package. Each independently read and freshly rebuilt all 47 mathematical modules and checked all 20 complete reference types and permitted axiom closures. Separate [fidelity completion](reviews/ie22-final-fidelity-evidence/completion-review.md) and [correctness completion](reviews/ie22-final-correctness-evidence/completion-review.md) reviews audit the actual Linux evidence. Reviewer audit-generator failures, additive corrections and harmless audit-only unused-binder warnings are preserved and disclosed.

The [operational report](verification/linux/OPERATIONAL-REVIEW.md) binds publication source commit `c45f9ccef20a2fa5cc4b988e93d4173dab853362`, all 394 input files, authenticated dependencies, actual isolation and rejection controls, and all 20 successful exports. Its distinct guest verification commit records an identical project snapshot. Audit the retained evidence with:

```
python3 linear-systems-and-elimination/IE-22/lean/verification/linux/audit_evidence.py
```

To reproduce from the repository root on the documented [non-root Linux environment](../../../docs/lean/README.md):

```
tools/lean/bootstrap.sh /absolute/path/to/verification-tools
tools/lean/verify.sh linear-systems-and-elimination/IE-22/lean /absolute/path/to/verification-tools
```

The pinned toolchain is Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. The shared source lock pins Comparator and control tools. The successful run reused the pinned Mathlib dependency cache and freshly rebuilt all project proofs. Current README and metadata record completed gates; their earlier pending versions remain in the immutable Linux input snapshot. Proofs, frozen statements, pins and build configuration are unchanged.
