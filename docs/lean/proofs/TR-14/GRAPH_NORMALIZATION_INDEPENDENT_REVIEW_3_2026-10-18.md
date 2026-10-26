# TR-14 actual independently normalized ordinary graphs — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I authored neither new module. **APPROVE these exact support sources.** No full ordinary lower-bound or Target proof is asserted.

| Module | SHA-256 |
| --- | --- |
| `UnitProductScaling` | `f94f28ce681078bc0ebb36266cd800a1ad211f1a5cc36aa17244cb2cee2a7ca4` |
| `GraphNormalization` | `5a3f0f5ff62e0fd7f61dea0252c9660c4f4c27a3790a64f46177e72337fc00d6` |

`UnitProductScaling` proves actual finite products of separately unit-scaled spaces equal the original product scaled by the actual product of units. The empty product is handled correctly. An actual unital algebra homomorphism maps unit scaling to scaling by the corresponding mapped unit. Consequently a projected subspace equal to top remains top after normalization, using the explicit unit-multiplication equivalence. There is no supplied projection-invariance or product identity oracle.

`GraphNormalization` defines mode k as the actual old graph scaled by a_k inverse, where a_k is an actual unit. Membership of that unit in the old graph is the precise premise ensuring one belongs to the normalized graph; existence is proved separately by OrdinaryGraphUnits. The total normalized product is the old product scaled by the inverse total unit. The new functional composes the original graph functional with multiplication by the total unit in the opposite direction. Thus annihilation is preserved by an exact inverse operation, rather than incorrectly leaving the old functional unchanged.

On the first algebra factor, the normalized functional is the old Frobenius functional multiplied by the first component of an actual unit, so its original nondegeneracy survives unit cancellation. The full scalar-coordinate projection survives actual invertible unit scaling, using the previously proved unrestricted ordinary-summand independence argument. Every scalar basis coefficient of the normalized functional is minus the corresponding actual total-unit scalar coordinate; it is nonzero from the unit inverse equation. This exact nonzero coefficient statement is the one later needed to exclude scalar-only primitive blocks. The proof does not require any original factor entry, including its constant coordinate, to be nonzero. Scalar-coordinate families may be empty and all identities keep their literal meanings.

The actual ordinary decomposition and quotient moment identity remain explicit where required for annihilation. The chosen units and their graph membership remain explicit data supplied by the earlier existence theorem. The module does not replace the frozen Target with a chosen-coordinate or general-position condition.

Independent immutable verification passed **13 Lean commands**, 12 actual sources plus a consumer, **70 explicit declarations** and **60 theorem/lemma-kind checks**. All constants pass LeanCert kernel trust and printed transitive axiom checks with only propext, Classical.choice, Quot.sound. All source bytes and ten pinned dependency trees pass before/after. Every local output object is rebuilt in a fresh private prefix excluding campaign project objects; pinned dependency objects alone are reused.

```bash
python3 docs/lean/proofs/TR-14/verification/check-graph-normalization.py \
  --top GraphNormalization --evidence-name graph-normalization-review-3
```

The exact driver, frozen sources/consumer, hashes and raw logs are in [verification/graph-normalization-review-3/](verification/graph-normalization-review-3/). Earlier minimum, graph, graph-unit and unit-scaling semantics retain their separate reviews. This is independent source review and local macOS Lean4.33.1 evidence, not full Target proof, Linux Comparator acceptance, source-author endorsement or external human peer review. No proof, original statement, permanent ID or canonical page was changed.
