# SP-11 diagonal uniqueness — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I did not implement `DiagonalUniqueness.lean`. **Verdict: approve**, source
SHA-256 `e5ccc886ef054e7d4e39a45a867b2621a5e973836aa0979744919aa30dea3385`.

For identical root labels, every actual predecessor is below the root, so
the canonical insertion position is its arity. Inserting the cap at the last
slot leaves all input colors equal to ordinary child indices, on both sides
of the pair. `canonicalLate_diagonal_input_val` proves this also for the
later root, rather than assuming the two constructions are definitionally
identical.

The generic `normal_tree_blockers` proves the actual local blocker condition.
At a top root, a smaller cap color is the output of the child with that index;
its label is strictly earlier and its actual color is distinct by local tuple
injectivity. At a nonroot occurrence, the actual parent is constructed and
earlier siblings provide the blockers. Zero arity causes no missing case:
there is no natural color below its canonical cap zero.

`canonicalPair_diagonal_unique` applies those blockers separately to the two
actual trees and then invokes the already reviewed class-histogram recovery
theorem. Repeated occurrences, including the identical labels at the two
roots, are retained in class sums. The result concerns the actual paired
summand index: any nonzero-sign coloring with the same actual shared-variable
exponent is the canonical pair. Its remaining assumptions are `OrderedGreedy`,
the actual ambient arity bound, the candidate's nonzero sign and equal
exponent. There is no unproved blocker or noncancellation premise in this
diagonal theorem.

Fresh immutable-source verification passed **36 Lean commands**: 33 proof
modules, two frozen statement/infrastructure modules and a separate consumer.
The consumer checks **268 explicit named declarations**, including **181
theorem/lemma constants**, for theorem kind where appropriate, LeanCert
kernel trust and transitive axioms. All source hashes remained unchanged;
all ten dependency pins and tracked-source cleanliness checks passed before
and after. Only accepted foundational axioms occur.

```bash
python3 docs/lean/campaign-2026-10-17/verification/check-sp11-tree-color-support.py \
  --evidence-name sp11-diagonal-uniqueness-review \
  --top DiagonalUniqueness GramCoefficient PriorInsertion AugmentedColors
```

Source snapshots, raw logs, generated consumer and machine-readable results
are retained in `sp11-diagonal-uniqueness-review/`. This is fresh local macOS
source elaboration with pinned cached dependencies and LeanCert kernel-trust
checks. It is not Linux Comparator evidence. This checkpoint proves diagonal
summand uniqueness; edge uniqueness and the full frozen SP-11 `Target` remain
outside its scope. Self-authored transitive support modules receive runtime
evidence here and separate independent source reviews from other agents.
