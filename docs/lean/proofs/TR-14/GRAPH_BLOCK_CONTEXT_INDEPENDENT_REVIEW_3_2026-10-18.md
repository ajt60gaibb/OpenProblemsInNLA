# TR-14 actual graph complements and block mode dimensions — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026. I authored no TR-14 proof source. **APPROVE** the following exact sources:

| Module | SHA-256 |
| --- | --- |
| GraphQuotientContext | `80244257e8996d93f97724ddb7409871e56e925057058bf78c51f188d2d200da` |
| GraphListContext | `c8d07951970aee22002140bcddf3681b266c63a5086c46b146b516112b9698b0` |
| GraphBlockModeDimension | `94c3e5efe8e15769b0a0b5b802a99054488881699f6b0c6a229a400cca28aa1f` |

The actual quotient mode range contains the identity via its degree-zero coefficient. The first image of a product of graph mode spaces is the corresponding power of that range. The list formula counts occurrences, so repeated indices retain their multiplicities. Inverse multiplication by the independently chosen actual graph units preserves first-image surjectivity. The proved quotient-power spanning criterion therefore supplies actual surjectivity for each complement with exactly `m-1` modes. The bound on the least apolar degree implies the required `(m-1)*q+1` bound for every allowed `m≥3`; no degree-at-most-mode-dimension assumption is inserted.

`GraphListContext` identifies each complement as the actual take/drop list at the same position. Its explicit finite-index take/drop list has length `m-1`, and its mapped product is exactly the original complement product. This supplies the surjectivity hypotheses needed by contextual iteration for every actual mode, including first and last positions.

For an actual idempotent, `GraphBlockModeDimension` identifies the ambient image of the corner quotient mode range with the polynomial coefficient image multiplied by that same idempotent. The injective corner inclusion preserves finite rank. The previously proved orbit-prefix result gives the exact first-image rank `min(q+1, dim actual corner)`. The actual first image of a normalized graph corner is the image of this space under an invertible unit multiplication, so its rank is unchanged. Projection rank is at most the full graph-corner rank, which yields the required mode lower bound. This argument does not assume a favorable block dimension or nonzero coordinate-zero entries in an ordinary summand.

Independent immutable verification passed **40 Lean commands**: 39 actual local sources and a separate consumer. The consumer checks **254 explicit declarations**, including **197 theorem/lemma kinds** and 16 actual private constants (13 theorems, two definitions, one abbreviation). All pass LeanCert kernel trust; printed transitive axioms are contained in `[propext, Classical.choice, Quot.sound]`. Every local object is rebuilt in isolated outputs; only pinned dependency objects are reused. All source bytes and ten dependency revisions/tracked trees remain unchanged before/after.

```bash
python3 docs/lean/proofs/TR-14/verification/check-graph-block-context.py \
  --top GraphListContext GraphBlockModeDimension \
  --evidence-name graph-block-context-review-3
```

Frozen source and driver snapshots, generated consumer, hashes and raw logs are retained in [verification/graph-block-context-review-3/](verification/graph-block-context-review-3/). No proof, original page, frozen statement or permanent ID was edited. This is independent local source/kernel evidence for these support gates; it does not itself claim the full TR-14 Target, Linux Comparator acceptance or external human peer review.
