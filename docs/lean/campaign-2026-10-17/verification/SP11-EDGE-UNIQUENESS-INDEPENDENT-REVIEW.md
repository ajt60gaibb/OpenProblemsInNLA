# SP-11 edge uniqueness — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I did not implement these modules. **Verdict: approve** at these source hashes:

| Module | SHA-256 |
| --- | --- |
| `TopOccurrences` | `5b7109a544fe220f43363c23ac7b23b5cee0f57d3f1aaa6e4c42cf379930f133` |
| `EdgeUniqueness` | `7ba36de0cfcf652fbd1537a52979d2f7345be68d60aabfa9283a04cec2aa46db` |

The augmented top list consists exactly of the earlier root at the true
insertion position and the later root's actual children in the remaining
`succAbove` positions. Adjacency excludes a duplicate earlier-root label from
the later predecessor list, so its labels are strictly increasing. The
canonical output values equal the augmented indices. Actual output
injectivity comes from reindexing the later root's own incident tuple; both
roots use its same cap. No independent variable or extra occurrence is added.

This augmented list is essential: the earlier root's cap can exceed its own
arity, so its own children would not supply every smaller canonical color.
The implementation correctly uses the augmented list for that root and for
all direct children of the later root. Its earlier slots provide actual
earlier-label blockers at every smaller color. All other nonroot occurrences
use their actual parent and ordinary earlier siblings. The later root is
tied to the earlier root through the common cap, with a strict label decrease
from `i < j`. These cases cover every actual paired occurrence.

Consequently `canonicalPair_edge_unique` discharges the complete blocker/tie
condition and proves equality of the actual paired summand index whenever its
nonzero sign and shared exponent match the canonical pair. Its graph
assumptions are exactly ordered greediness, ambient arity bounds and an
ordered adjacent root pair. No noncancellation oracle remains in this result.

Fresh immutable-source verification passed **38 Lean commands**, covering 35
proof modules, two frozen statement/infrastructure modules and a separate
consumer. All **286 explicit named declarations**, including **196 theorem or
lemma constants**, passed theorem-kind checks where appropriate, LeanCert
kernel trust and transitive axiom checks. All ten dependency pins/tracked
sources passed before and after, and all frozen source bytes were unchanged.

```bash
python3 docs/lean/campaign-2026-10-17/verification/check-sp11-tree-color-support.py \
  --evidence-name sp11-edge-uniqueness-review \
  --top EdgeUniqueness DiagonalUniqueness GramCoefficient PriorInsertion AugmentedColors
```

Exact source, generated consumer, raw logs and machine-readable evidence are
in `sp11-edge-uniqueness-review/`. This is local macOS kernel evidence using
pinned cached dependencies; it is not a Linux Comparator run. This snapshot
includes diagonal uniqueness and the coefficient bridge, but predates the
later `Final` target wrapper. Self-authored transitive supports are runtime
audited here and have independent source reviews by other agents.
