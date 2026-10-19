# TR-14 genuine corner quotient and product algebras — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I authored neither new source. **APPROVE these exact algebra support modules.** No ordinary lower bound or full Target is asserted.

| Module | SHA-256 |
| --- | --- |
| `IdempotentCorner` | `e96d2e7e6d6d43b1793d717a13f329f3979628ac3ecb42fa720372f615fe5b78` |
| `CornerProduct` | `6a1b5920f946ba73eb8ccd3fabc3ddb9b1c2d811585b9ad643033a4cd4e955bd` |

`IdempotentCorner` is the actual unital algebra B/ideal(1−e). For an actual idempotent e, multiplication by e kills this ideal and hence defines a well-defined K-linear ambient inclusion. The projection-zero equivalence proves its kernel exactly: e*x=0 implies x=(1−e)*x is in the quotient ideal, while the forward direction follows by the actual inclusion. This proves inclusion injectivity, not a supplied dimension fact. Its image is precisely the actual multiplication range eB. The constructed linear equivalence to that range gives the stated intrinsic/ambient finite-rank equality without a finite-dimensionality premise. The ambient inclusion sends the corner identity to e and preserves multiplication; it is correctly not advertised as a unital algebra map into B. Algebra homomorphisms induce actual corner quotient homomorphisms because they kill the defining generator in the corresponding quotient.

`CornerProduct` combines the genuine induced factor maps to construct the product-corner map. Its kernel is zero by the two factor projection-zero equivalences and its surjectivity uses actual quotient representatives in each factor. The resulting algebra equivalence identifies the corner of A×C with the product of the two actual factor corners, and its compatibility with ambient inclusions is proved on representatives. No nonzero factor or proper-ideal assumption is added.

Reducedness is transferred through the injective multiplicative ambient inclusion using positive powers. Since the corner identity maps to e rather than ambient one, the proof deliberately does not use an invalid power-zero preservation claim. A nilpotence witness n is replaced with n+1, so the positive-power identity applies even when the original witness exponent is zero. Ambient reducedness then kills the inclusion and injectivity kills the corner element. This covers e=0 and its zero-ring corner, e=1, zero factor corners, and even a subsingleton ambient ring. The ground field K and commutative algebras remain genuinely generic; reducedness is required only in the dedicated reducedness theorem.

Independent immutable verification passed **five Lean commands**: four actual sources and a separate consumer, **37 explicit declarations** and **27 theorem/lemma-kind checks**. All explicit constants pass LeanCert kernel trust and transitive printed axioms; only propext, Classical.choice, Quot.sound occur. All frozen bytes and ten dependency pins/tracked trees pass before/after. All local objects are freshly rebuilt in a private output prefix excluding campaign project objects, reusing only pinned dependency objects.

Reproduce from the repository root:

```bash
python3 docs/lean/proofs/TR-14/verification/check-corner-algebra.py \
  --top CornerProduct --evidence-name corner-algebra-review-3
```

Exact driver/source/consumer snapshots, compiler/pin identities and raw logs are in [verification/corner-algebra-review-3/](verification/corner-algebra-review-3/). The imported product-stabilizer source retains its earlier review. No proof, statement, original canonical page or permanent ID was edited. This is independent source review and local macOS Lean4.33.1 kernel evidence, not full Target proof, Linux Comparator acceptance, external human peer review or source-author endorsement.
