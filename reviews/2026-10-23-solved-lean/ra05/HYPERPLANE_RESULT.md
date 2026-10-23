# Exact RA-05 hyperplane support: local kernel replay

Three exact, independently pre-reviewed support signatures are now implemented in `NLA/Proofs/RA05/HyperplaneBridge.lean`:

- `unitHyperplane_projector` proves that `I - xxᵀ` is a symmetric idempotent of rank at most `d-1` for every real unit vector in every positive finite dimension, including `d=1`.
- `rowCost_unitHyperplane` identifies the actual RA-05 row residual cost with the actual RA-06 absolute row action to the same real power, for arbitrary real `p`.
- `strongCoreset_implies_allVectorEmbedding` transfers every actual strong coreset for rank `d-1` to the actual all-vector lp energy guarantee, preserving the original matrix, arbitrary nonnegative weights, exponent `p>0`, and real accuracy. It handles both zero and nonzero test vectors and introduces no full-rank or sampler restriction.

The implementation imports the reviewed definitions; it does not import `Challenge.lean`. No admitted theorem, auxiliary axiom, `native_decide`, or external numerical certificate occurs in its proof. The three selected exports passed `#assert_trust kernel` under pinned LeanCert; `#print axioms` returned exactly `propext`, `Classical.choice`, and `Quot.sound` for each.

`verification/support/result.json` records a fresh local Lean 4.33.1 source build of the six-file closure, using isolated temporary NLA objects and the existing pinned dependency cache. Logs retain every selected kernel/axiom check. `IMPLEMENTATION_LOCK.json` records the source hashes. Reproduce from the repository root with:

```bash
python3 reviews/2026-10-23-solved-lean/ra05/check_support.py \
  --lean /private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean \
  --packages /Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages
```

This is a local macOS source/kernel replay, not a Linux CI or Comparator receipt. Root integration must independently bind and replay the exact committed package before claiming those checks. The dependency cache is read-only; no compiled objects are retained in this packet.

RA-05 remains Solved. Its complete `Classification ∧ NegativeAnswer` is unproved in Lean. The support bridge enables reuse of the existing RA-06 deterministic complete-graph obstruction, but the sampler-specific RA-06 final theorem alone cannot refute arbitrary weighted RA-05 coresets. The rate calculation and remaining all-p Fourier/partial-coloring gates are stated in the unchanged `SUPPORT_CONTRACT.md`. No original, ID, canonical page, or preexisting dirty file was changed.
