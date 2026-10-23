# Independent final review of the RA-05 support proofs

Reviewer: OpenAI Codex AI agent `/root/verification`, 23 October 2026.
Verdict: **approve the eleven support exports at the source hashes below**.
I authored neither implementation. This is independent AI-agent review of
scope, correctness, reuse, and actual local mechanical evidence; it is not
external human review or approval of RA-05's complete Target.

I read the original canonical RA-05 question and its retained exact statement
specification at published commit `5487945e5a72abd952b0c89915915de8cc9b3e65`,
the concrete published RA05/RA06 definitions, both Challenges, the minimum
contract and both pre-proof reviews of the hyperplane bridge, and the actual
two implementations. My earlier minimum pre-review is recorded separately in
`ra05-minimum/PRE_REVIEW_VERIFICATION.md`. Both reference Challenges retain their
approved bytes. The canonical originals and all permanent IDs are unchanged.

The eight minimum-support proofs follow the concrete definitions faithfully.
`Real.sqrt_nonneg` and `Real.rpow_nonneg` establish row positivity for every
real exponent. `Finset.sum_nonneg` gives total positivity. Unit weights give
the exact cost for every matrix P, so their multiplicative inequalities follow
from nonnegative accuracy even if it exceeds one. Their support cardinality is
exactly n, including n=0. `csInf_le'` uses an actual feasible weight witness.
`csInf_mem` uses the explicitly constructed all-one witness to prove that the
natural budget set is nonempty; the opposite support inequality then proves
attainment with equality. `le_sSup` embeds the very same finite matrix and
dimensions in the complete-lattice ENNReal supremum. No unbounded real-supremum
default, assumed minimizer, compactness oracle, or target theorem is imported.

The three hyperplane proofs also match the approved mathematics. The actual
matrix is identity minus the outer product of the same unit vector. Symmetry
and idempotence are finite matrix algebra. It kills that nonzero vector; the
kernel therefore has positive real dimension, and rank-nullity proves rank at
most d-1, including d=1. The row residual is exactly `(RowValue A i x) * x`;
the unit squared norm and `Real.sqrt_sq_eq_abs` establish the row-cost equality
before applying the same arbitrary real exponent. The all-vector theorem
handles y=0 using p>0 and `Real.zero_rpow`, and normalizes every nonzero y by its
strictly positive Euclidean norm. Both weighted and unweighted energies scale
by the same real power of that norm. Multiplying the unit inequalities by this
nonnegative factor is valid for every real epsilon. The same matrix, weights,
exponent and accuracy are retained. Empty row sets and rank-deficient inputs
remain allowed. The proof uses RA06's literal RowValue and InputEnergy
definitions; it imports no sampler-failure claim as an arbitrary-weight lower
bound.

Mathlib supplies the real-power, finite-sum, conditional-infimum, complete-
lattice, matrix, and rank-nullity APIs used here. Small algebra/normalization
helpers are private, while the eleven reusable conclusions have explicit
names. No numerical certificate is mathematically needed for these exact
arguments. No source theorem is silently replaced or relabelled as a full
classification. The code is ordinary new support implementation; the original
problem and resolution source authors retain their existing credits.

I independently froze the two packets into `ra05-combined/`. Its INPUTS.json
binds every copied source to its author packet; the RA05 and Infrastructure
copies from both packets were additionally byte-compared and matched. The two
original Challenges are imported only by the combined Challenge wrapper. The
Solution wrapper imports only the actual proof modules. I then replayed all
sources into a fresh temporary object directory, generated the latest published
harness's theorem-kind/LeanCert kernel consumer for the exact eleven exports,
and ran the unmodified pinned Comparator library on separately imported
Challenge and Solution environments. All **22 actual statement/axiom checks**
passed: the eleven exact theorem types and all referenced definitions matched,
and each transitive axiom closure was contained in `propext`, `Classical.choice`,
and `Quot.sound`. The generated consumer required each export to be a theorem
constant, passed `#assert_trust kernel`, and printed exactly those three axioms
for every export. All 16 Lean commands exited zero.

The complete independently executed receipt, raw outputs, source snapshots and
commands are under
[`actual-comparisons/attempt-yiz5d36d/`](actual-comparisons/attempt-yiz5d36d/).
Its result.json records the package pins and clean tracked-source checks before
and after, input hashes, and removed temporary compiled objects. Reproduce from
the repository root with:

```bash
python3 reviews/2026-10-23-solved-lean/verification/compare-support.py \
  --lean /private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean \
  --packages /Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages \
  --packet reviews/2026-10-23-solved-lean/verification/ra05-combined \
  --config reviews/2026-10-23-solved-lean/verification/combined-comparison.json
```

| Reviewed source | SHA-256 |
| --- | --- |
| SupportMinimum.lean | `d21474d121f82481cf7de107ecaa8405d0b2d12cf60c08ef75fcbea471c1f0ce` |
| HyperplaneDefinitions.lean | `03c589f029a146203487f4d5ed5982eb67e4a91d64c0ab8f817baf1de898a276` |
| HyperplaneBridge.lean | `2e8d441f6aa46d7344c37762010be9e1afb30574e085bad980bb9bf01e7ccae1` |
| MinimumChallenge.lean | `6bf0be68c5353fb3d20e48ae6b46fc9b601646309bafa70612708c7d84fcf5f0` |
| HyperplaneChallenge.lean | `0049b6258325a138e0579fd26fcacc772758996f77c3cc9211a3e58a3663ff12` |
| published RA05.lean | `3438fe4ca2bcf313f3336c94f6a2105b83ee918b5d266009efc0c4f76c121e1e` |
| published RA06.lean | `865af15803905e04de1202266f5af75fc5486b8345fdba25a44052202742883d` |
| published Infrastructure.lean | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |

There are no requested proof changes. The mechanical evidence trusts the
reviewed dependency object cache and uses local macOS Lean elaboration plus
the unchanged Comparator library. It does **not** execute the authoritative
Linux Comparator executable, exporter, isolation controls, or separate raw
kernel replay. The existing 9-check Comparator fixture receipt and deliberate
sorry/native/kind rejection controls are retained separately. A committed
canonical package still requires its own metadata validation, isolated Linux
verification, exact final source correspondence, and publication checks.

These exports prove support facts only. They prove neither Classification nor
the universal NegativeAnswer, and therefore do not prove `NLA.Statements.RA05.Target`.
RA-05 must retain Solved status and its original mathematical target.
