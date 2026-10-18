# TR-14 product stabilizers, contextual reducedness and unit spans — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I authored none of these modules. **APPROVE the following exact conditional support gates.** No ordinary product dimension inequality or full TR-14 Target is proved by this checkpoint.

| Module | SHA-256 |
| --- | --- |
| `ProductStabilizer` | `fbbeb013e7d6872681cdc2598051b0bd178423e37fa8a477bccc4fc26852f98a` |
| `ContextualReduced` | `62d2b125bcaf2db2a8d09d3b0bd713ea9b59c5dba84a62b980a1fb18d6ecfd76` |
| `UnitSpan` | `10ec655e20cee3c33b1023dcfc795c25e96deb2914ea90dba5b55768a9b909b7` |

`ProductStabilizer` defines the actual unital subalgebra of multipliers preserving a given subspace. Its product with that subspace is exactly the subspace: stability proves one inclusion and multiplication by one proves the reverse. Stabilizing action passes to actual span-of-products factors by multiplication induction, including zero spaces. Multiplication by a unit is an explicit linear equivalence with inverse multiplication; its actual image subspace preserves finite rank, and inverse scaling sends a chosen unit to one. The one-containing subspace inclusions and final-tail stabilizer inclusion are ordinary multiplication facts. No dimension lower bound, generic product behavior or structural decomposition is assumed or advertised.

`ContextualReduced` proves a nilpotent exclusion from explicit contextual data. Projection to the reduced factor kills the nilpotent's second component. Full first-factor projection supplies every test multiplier in the first algebra; stability/annihilation sends the translated products to zero under the stated functional. The actual Frobenius nondegeneracy condition kills the first component times the chosen unit, and unit cancellation kills the first component. This proves actual reducedness of the given subalgebra. The stabilizer case uses its genuine action and the auxiliary case uses the explicit `S*T ≤ T`, translated `a*V ⊆ T` and `T*Q ≤ W` conditions by multiplication induction. The Frobenius condition, full projection, reduced second factor, functional annihilation and first-component unit remain visible hypotheses. They must be established for the later moment-algebra application. The module does not assert that all subalgebras of a nonreduced ambient algebra are reduced or form a finite set.

`UnitSpan` identifies the actual algebra spectrum with that of the faithful multiplication representation. Finite-dimensional operator theory gives a finite exceptional scalar set, and an infinite field gives a scalar translate of any element that is an actual unit. If a subspace contains one, both the scalar multiple of one and that unit translate lie in the span of its units, so their difference gives the original element. The reverse inclusion is by construction. This is valid without reducedness of the ambient algebra or a finiteness assumption on its subalgebras. Finite dimension, infinite ground field and membership of one remain the exact explicit conditions.

Independent immutable-source verification passed **five Lean commands**: the three support files, statement infrastructure, and a separate generated consumer. It checks **22 explicit declarations**, including **19 theorem/lemma constants**, theorem kind, LeanCert kernel trust and transitive printed axioms. Only `propext`, `Classical.choice`, `Quot.sound` occur. All source bytes and all ten dependency pins/tracked trees passed before/after. Local project objects are built into a fresh private output prefix and campaign project objects are excluded; pinned cached dependency objects are reused.

Reproduce from the repository root:

```bash
python3 docs/lean/proofs/TR-14/verification/check-product-support.py \
  --top ContextualReduced UnitSpan --evidence-name product-support-review-3
```

The exact driver, sources, generated consumer, hashes and raw logs are in [verification/product-support-review-3/](verification/product-support-review-3/). This approval is independent mathematical/source review of these three files and local macOS Lean4.33.1 kernel evidence. It is not a lower-bound theorem, full Target proof, Linux Comparator receipt, source-author endorsement or external human peer review. No proof module, permanent ID, original target or canonical page was changed for this audit.
