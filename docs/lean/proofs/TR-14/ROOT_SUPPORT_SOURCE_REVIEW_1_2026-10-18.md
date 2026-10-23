# Independent root-support review 1 — 2026-10-18

Reviewer: `/root/solved_inventory`, an OpenAI Codex AI agent, independent of the eight module authors. **APPROVE** the eight exact source modules below. This is a source/mathematical-fidelity review plus a fresh local macOS kernel replay of their full local import closure. It does not assert a full TR-14 proof, Linux acceptance, Comparator acceptance or human peer review.

| Module | SHA-256 |
| --- | --- |
| ContextualIteration | `f3414dc6a43fa95c265b2097d90cd3024001f7c169e2e5f8d2ccc506b6991f5f` |
| IdempotentCorner | `e96d2e7e6d6d43b1793d717a13f329f3979628ac3ecb42fa720372f615fe5b78` |
| CornerProduct | `6a1b5920f946ba73eb8ccd3fabc3ddb9b1c2d811585b9ad643033a4cd4e955bd` |
| CornerContext | `f1de8589c8e0f13baaaaac6fd2df3233c257bcbb00181879b081aec327632ad1` |
| CornerStabilizer | `8c0fbebebf4a0731a3bea9b0c19128cb6c401f3ffead3f63a27bb5d1caef5ccd` |
| NumericalBlockLower | `a6cc22b3248cb4f65f2c1bef58d4ad2566b384c1a80b79c6df6f6dca1ab332b9` |
| QuotientProductSpan | `6c65f76dcdf65880f7edcd5596049dc5c6dc1af8cf573f59237156dcbd6be355` |
| ChartUpperConstruction | `a03aeeb3155df3bde6a1e3d91a1f1a63e26c3e60b4982b1ae6f6703c053d768a` |

I read each full source and checked these actual proof gates. `ContextualIteration` passes the actual take/drop projection context to successive product inequalities and bounds each prefix stabilizer by the full stabilizer. The nonempty-list and one-containing hypotheses are explicit; the scalar-stabilizer specialization is proved. `IdempotentCorner` constructs the quotient by `(1-e)`, its injective multiplication-by-e inclusion, and its actual linear equivalence to the multiplication range; no unital structure is assigned to the ambient nonunital ideal. `CornerProduct` proves the actual product-corner equivalence and reducedness inheritance, including a zero corner. `CornerContext` transports actual product subspaces and functionals, retaining the multiplication, one, annihilation, Frobenius and projection identities. `CornerStabilizer` extends an intrinsic block stabilizer element to the ambient algebra and uses the actual primitive-block scalar action, proving the intrinsic stabilizer has dimension at most one rather than assuming it.

`NumericalBlockLower` is a finite natural-number arithmetic gate with explicit actual block inequalities, dimension sums and support count; its large-block and all-small-block cases justify both subtractions and the minimum. It supplies no block existence premise. `QuotientProductSpan` derives the full quotient product span from the actual root-power basis and elementary exponent splitting, including zero exponents. It imposes no block-dimension-at-most-n restriction. `ChartUpperConstruction` chooses an actual least apolar degree, normalizes one actual chart, preserves the full smaller-kernel minimality conditions and nonzero data, and produces both symmetric widths for the original-coordinate tensor using that same polynomial/chart. No mathematical blocker was found in these exact sources.

The immutable replay rebuilt 60 actual local source modules and a generated declaration consumer (61 commands) into fresh temporary outputs. It reused only clean, pinned external Mathlib/LeanCert dependencies and did not load campaign NLA objects. The consumer checked every 355 explicitly named declaration in this closure, including 272 theorem/lemma-kind checks, LeanCert kernel trust and the permitted standard-axiom set. Every command passed; every source was unchanged after replay. The exact pins, executable hash, commands, per-source and per-log hashes, source snapshots, explicit declaration list and before/after dependency checks are retained in [the result](verification/inventory-root-support-review-1/result.json). The generic consumer file is historically named `IndependentTreeColorAudit.lean`; its retained content contains only this TR-14 closure's declarations.

Reproduce from the repository root:

```bash
python3 docs/lean/proofs/TR-14/verification/check-inventory-independent-root-support.py --evidence-name inventory-root-support-review-1 --top ContextualIteration IdempotentCorner CornerProduct CornerContext CornerStabilizer NumericalBlockLower QuotientProductSpan ChartUpperConstruction
```

The driver snapshots the sources it is run against; the retained result binds the reviewed version. This reviewer authored ten imported dependency modules listed in the result. Rebuilding those dependencies is mechanical kernel evidence and does not count as independent source approval of them. This report's independent approval is restricted to the eight named modules; other agents' reports cover reviewer-authored sources.

Result SHA-256: `50fc4226d0725214ab15f1a441645f413c80b6a6785f8b0d54dbe429885164bf`.
