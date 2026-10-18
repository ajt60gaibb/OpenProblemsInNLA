# TR-14 inherited primitive-corner inequalities — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026. I authored no TR-14 proof source. **APPROVE `CornerInheritance.lean` at SHA-256 `b671205fdaea4bcb2e139c072d40e9f9c5ce302eca062fc898936399deafdbb4`.**

Every actual take/drop complement projection descends through the genuine corner quotient algebra map. The proved list-product image identity preserves the actual list and index. Surjectivity is constructed by quotient representatives, rather than assumed for a new block list.

The intrinsic corner functional is nonzero whenever the actual first idempotent component is nonzero. Otherwise testing all projected ambient first-factor values would force the original Frobenius functional to annihilate multiplication by that component, contradicting its nonzeroness. This also handles a zero scalar corner; no nontriviality of both factors is silently assumed.

For an actual primitive indicator of the actual full-product stabilizer, the inherited list meets the contextual inequality's hypotheses: contains one, inherited Frobenius restriction, actual annihilation, every complement first projection onto, and scalar stabilizer dimension at most one. The last fact is derived from the primitive scalar-action theorem for the same algebra equivalence, not supplied as a trivial-stabilizer oracle. The ambient moment algebra is permitted to have nilpotents; reducedness is needed only for the scalar factor and is proved for its corner.

The actual block product lies in the kernel of its nonzero intrinsic functional, so its dimension plus one is at most the sum of the two actual factor dimensions. Combining this with the contextual list bound gives `length L*d+2 ≤ dim A_corner+dim C_corner+length L`. The explicit hypothesis `d≤finrank U` for each actual mode remains a separate input in this module; `GraphBlockModeDimension` supplies it in the tensor application. No original-rank inequality, partition, support count or full Target is assumed here.

Independent immutable verification passed **21 Lean commands**: 20 actual local sources and a separate consumer, checking **110 explicit declarations** and **95 theorem/lemma kinds**. All pass LeanCert kernel trust and printed transitive axiom checks with closure contained in `[propext, Classical.choice, Quot.sound]`. There are no explicit private declarations in this closure. Local outputs are rebuilt in a private prefix excluding project build objects. All frozen sources and ten dependency pins/tracked trees pass before/after checks.

```bash
python3 docs/lean/proofs/TR-14/verification/check-corner-inheritance.py \
  --top CornerInheritance --evidence-name corner-inheritance-review-3
```

Exact snapshots, consumer/driver, hashes and raw logs are retained in [verification/corner-inheritance-review-3/](verification/corner-inheritance-review-3/). No source, original artifact, statement or permanent ID was edited. This is independent local macOS kernel evidence for this support module, not a Linux/Comparator or complete Target acceptance claim.
