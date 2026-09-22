# IE-21: complete kernel-verified spherical-row deletion limit

The complete canonical IE-21 target is Lean verified. All 23 independently reviewed required declarations passed the actual non-root Linux Comparator, authentic LeanCert kernel-trust assertions and default-kernel replay. Their transitive axiom closures contain only `propext`, `Classical.choice` and `Quot.sound`.

The proof covers the exact floor-row deletion minimum, the actual Euclidean operator norm, normalized surface-law rows, the literal Gaussian integral, explicit finite-size bounds, and every sequence with dimension and aspect ratio tending to infinity. Arbitrary changing probability spaces, rank-deficient maps and empty retained selections are included. It uses exact analytic reasoning without approximate quadrature or finite numerical sampling. The separate deterministic universal-constant target IE-22 is not claimed by this package.

Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. Original mathematical proof: **Matthew J. Colbrook**. The canonical statement, original attribution and dated manuscript remain preserved. Substantial AI assistance and all author/reviewer roles are disclosed in [formalization.yaml](formalization.yaml); no human peer review or official Tau Ceti endorsement is claimed.

The [23-statement boundary](Challenge.lean) was reviewed independently before implementation. Definitions, Challenge, NUMERICAL_TARGETS and comparator.json remain byte-identical to [their preproof freeze](reviews/statement-freeze.json). Their original draft wording is historical. Challenge's 23 deliberate placeholders specify reference types and are never imported by the proof modules. Solution explicitly chooses LeanCert kernel trust and checks every selected declaration.

The complete source was independently approved by the [fidelity referee](reviews/ie21-final-fidelity-evidence/review.md) and [correctness referee](reviews/ie21-final-correctness-evidence/source-review.md), each of whom authored none of IE-21. Each independently rebuilt all 31 proof modules and checked all 23 exact reference types and permitted axiom closures. Their separate [fidelity completion review](reviews/ie21-final-fidelity-evidence/completion-review.md) and [correctness completion review](reviews/ie21-final-correctness-evidence/completion-review.md) audit the actual Linux evidence. The local audit-only linter warnings and resolved packaging findings are disclosed in the original review records.

The [operational report](verification/linux/OPERATIONAL-REVIEW.md) binds the exact publication source commit `1eb284b84ecc0d3c958d022b3e020be7fa111391`, 289 input files, authenticated dependency revisions, every sandbox/rejection control and all 23 successful exports. The distinct guest verification commit records an identical project snapshot. Run the portable retained-evidence audit with:

```
python3 linear-systems-and-elimination/IE-21/lean/verification/linux/audit_evidence.py
```

To reproduce the actual verification from the repository root on the documented [non-root Linux environment](../../../docs/lean/README.md):

```
tools/lean/bootstrap.sh /absolute/path/to/verification-tools
tools/lean/verify.sh linear-systems-and-elimination/IE-21/lean /absolute/path/to/verification-tools
```

The pinned toolchain is Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. The shared source lock pins Comparator and control tools. The successful run reused the Mathlib dependency cache for the pinned revision and freshly rebuilt the project. The current README and metadata record completed gates; their earlier pending versions remain in the immutable Linux input snapshot. Proofs, reviewed statements and build inputs are unchanged.
