# Independent final RA-05 minimum-support review

Reviewer: OpenAI Codex AI agent `/root/inventory`, 23 October 2026. Author of
the proof and primary audit: `/root`. I independently reviewed the final source
and ran a separate four-command source replay; the proof author did not write
my replay script or logs. I previously pre-reviewed the same eight signatures.

**PASS as eight exact semantic support lemmas.** Their statements are unchanged
from the approved Challenge. No full RA-05 result or canonical status promotion
is warranted. The original Target still requires the asymptotic Classification
and the universal NegativeAnswer.

| Final reviewed input | SHA-256 |
| --- | --- |
| `NLA/Proofs/RA05/SupportMinimum.lean` | `d21474d121f82481cf7de107ecaa8405d0b2d12cf60c08ef75fcbea471c1f0ce` |
| `SupportAudit.lean` | `038b71ad99bba09cc0483429d7df9a355fdb858e6c3c4c76eb97ddb5f7343446` |
| `Challenge.lean` | `6bf0be68c5353fb3d20e48ae6b46fc9b601646309bafa70612708c7d84fcf5f0` |
| `CONTRACT.md` | `5055ea71b579eb464da47fced1ca95b7967b57e8694b948c65d62b487b0e94cc` |
| `verification/inventory-review/run_review.py` | `2ad3ea8017dd9a70b0389230f41bc38169cd46c3e11c89f27ffc832832981095` |
| `verification/inventory-review/result.json` | `73b23e9d9c456202db373d84ce933773381c9fc57d5a3e0726abc2bed7a3a805` |

The independent replay byte-compared RA05 and Infrastructure with immutable
published commit `5487945e5a72abd952b0c89915915de8cc9b3e65`, required all eight
theorem headers to equal the exact Challenge headers, snapshotted the four
compiled source files, and checked that all inputs remained unchanged after
the run. All checks passed. It used official Lean 4.33.1 compiler commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6` on local arm64 macOS, with the
shared pinned dependency caches recorded in result.json. All four commands
exited zero. Each of the eight `#assert_trust kernel` commands passed, and each
transitive axiom report contains exactly `propext`, `Classical.choice` and
`Quot.sound`.

The proof imports the actual retained definitions, two Mathlib libraries and
their kernel-checked dependencies. It does not import Challenge, fabricate a
minimizer, assume a coreset oracle or target, use a custom axiom, or call native
evaluation. The exact proof steps are sound:

- Nonnegative square roots and real powers give actual nonnegative row costs;
  finite summation gives total nonnegative cost for every real exponent.
- Unit weights are nonnegative and turn the weighted sum into the actual Cost
  for every projector. The two inequalities use `ε * Cost ≥ 0`. No projector,
  rank, dimension, sign or accuracy restriction is silently added.
- The exact support cardinality of unit weights is `n`, including zero rows.
- Any actual coreset gives a literal member of the natural support-budget set.
  `csInf_le'` yields the lower bound; there is no feasibility assumption hidden
  in a default empty-set infimum.
- Under nonnegative accuracy, the actual unit-weight witness makes the natural
  set nonempty. `csInf_mem` gives a budget witness, and the two opposite support
  inequalities prove that its support is exactly MinimumSupport. This proves
  attainment rather than assuming it.
- The same unit witness proves MinimumSupport ≤ row count. The final theorem
  puts the actual matrix and dimensions into the defining ENNReal supremum,
  so no boundedness or attainment of a real supremum is required.

This reuses the source's exact strong original-row coreset model. It includes
empty row and column sets, zero matrices, every natural rank, all real powers,
and zero accuracy where stated. For the final supremum bound the exact `k < d`
premise is retained; no coreset/accuracy premise is needed for that membership
fact. These helpers are useful foundations for future rate proofs, but supply
no dimension-independent size estimate, lower-bound example or rate
contradiction.

Reproduce my separate replay with:

```bash
python3 reviews/2026-10-23-solved-lean/ra05-minimum/verification/inventory-review/run_review.py \
  --lean /private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean \
  --packages /Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages
```

The saved runner, input hashes and source snapshots make this local source
replay reviewable. It reuses compiled dependency caches and is not a clean
dependency build, Linux sandbox/default-Comparator receipt, CI run, source-author
endorsement or human peer review. It does not establish truth by checking the
trust of a proposition definition: the eight inspected exports are actual
proved theorems. The canonical RA-05 status remains Solved.
