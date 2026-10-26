# Independent combined RA-05 support-package review

Reviewer: OpenAI Codex AI agent `/root/inventory`, 23 October 2026. Package
assembler and minimum-support author: `/root`. Hyperplane author:
`/root/proof_route`. I independently pre-reviewed and final-reviewed both support
components, and did not author either proof or this package's assembly.

**PASS for the exact staged canonical support project.** I inspected
`/private/tmp/nla-ra05-oct23-package` read-only, compared it with the approved
packets and published sources, checked exact export coverage, and independently
replayed all eleven source commands. This package must retain canonical status
Solved and `whole_problem_verified: false`. It proves eleven useful support
theorems; it does not prove the full RA-05 Target and supplies no basis for a
Lean-verified promotion.

## Bound package and evidence

`PACKAGE_REVIEW_INVENTORY_INPUTS.json` records every staged file hash, exact
published-source correspondence, approved proof hashes, all eleven selected
names and independent replay checks. Its SHA-256 is
`2ff53c54ee663e302923d117fe06bb27332017b83a6b02bfae437e278d3843a8`.
The reproducible read-only assembly checker is
`package-review-inventory/review_package.py`, SHA-256
`b2aa101ea2a6d629df480881b1a6cd200c46d6485610fc368ff6eb5d1bb2dc99`.

At review, the package contains 36 ordinary files and no symlinks or compiled
artifacts. `PACKAGE_LOCK.json` covers all other 35 files, with every file's
bytes and SHA-256 matching. The lock itself has SHA-256
`1a74a51de1768aa37710dce52bd6100ac2091dbee32c4e03cee43acb8be9cdef`.
The exact core assembly hashes are:

| File | SHA-256 |
| --- | --- |
| `Challenge.lean` | `7a311a87ee64b231a1ba27b744cf0cebc7b2b96632822db2e43784a7a124a622` |
| `Solution.lean` | `1c9c8965d18bfe982bf1fb73bbd308f76a6fda551887a07e559acee03860c20b` |
| `SupportAudit.lean` | `d75ac87c8671750c16f573f87c1555cacb7c74365efd070313348f525579aaa9` |
| `Identity.lean` | `627477b5f8f80099f19ba234bc6c0e9808e7fe599baf5bc30dac072c8d81f770` |
| `comparator.json` | `eaba2868d810c22b1222dbe85ebe1d24f9ba8031f850717acf11ba4b4288d94e` |
| `formalization.yaml` | `acf6121b4c21d4cafd206ca65f0371a7711a5398b0b477e862e06d1141a6a8f4` |
| `lake-manifest.json` | `b92de333f75f69ea9b5cf2033f5f2a2e763d349c17fe97312c1c5fbed815cdda` |
| `reproduce.py` | `69991017dd73c365fa827ecbc01d466908615ae6605fa482b149146716c54eec` |

Later insertion of review reports/evidence and regeneration of the enclosing
lock are reflexive packaging additions. This approval binds the inspected
proof, definition, Challenge, configuration and scope bytes; mathematical,
Comparator-selection or scope changes require renewed review.

## Exact retained mathematics and provenance

All three substantive files are byte-identical to their already independently
reviewed component packets:

| Source | Approved SHA-256 |
| --- | --- |
| `NLA/Proofs/RA05/SupportMinimum.lean` | `d21474d121f82481cf7de107ecaa8405d0b2d12cf60c08ef75fcbea471c1f0ce` |
| `NLA/Proofs/RA05/HyperplaneDefinitions.lean` | `03c589f029a146203487f4d5ed5982eb67e4a91d64c0ab8f817baf1de898a276` |
| `NLA/Proofs/RA05/HyperplaneBridge.lean` | `2e8d441f6aa46d7344c37762010be9e1afb30574e085bad980bb9bf01e7ccae1` |

The live RA05, RA06 and Infrastructure definitions, frozen Reviewed/RA05,
preserved original page, exact specification, both credited mathematical
manuscripts and toolchain are byte-identical to published commit
`5487945e5a72abd952b0c89915915de8cc9b3e65`. `sources/ORIGINAL.md` matches both
the canonical RA-05 README and the published preserved ORIGINAL. The original
page remains Solved. The frozen full Target is still exactly
`Classification ∧ NegativeAnswer`, and `Identity.lean` proves only its
definitional equality with the live proposition by `rfl`. It asserts no proof
of either proposition. IDs, canonical page paths and original mathematical
targets are not altered by this support package.

The dependency manifest differs from published `lean-statements` only in its
root package name, now `NLARA05Support`, matching the lakefile. Every one of its
ten dependency URLs and exact revisions is unchanged. The explicit Lean
toolchain is unchanged. There is no path dependency or floating direct
dependency revision. The historical branch names in inherited `inputRev`
fields are resolved by immutable manifest revisions.

## Complete support coverage and truthful scope

The combined Challenge's first eight theorem headers are exactly the approved
minimum-support headers; its final three are exactly the approved hyperplane
headers. Their namespaces and all binders/premises remain unchanged.
`comparator.json` selects all eleven distinct actual support names and no
definition holes. Metadata advertises exactly those same eleven declarations,
once each, pointing at the actual proof files. SupportAudit has exactly one
kernel-trust assertion and one complete axiom report for every selected name.

Solution imports the two actual proof modules and no Challenge. Challenge's
eleven deliberate holes remain separate reference statements. They do not
enter the solution import closure. The approved actual proofs retain their
arbitrary dimensions and parameters, actual natural minimum/ENNReal supremum,
genuine hyperplane projector, exact row residual and arbitrary original
nonnegative weights. No assumed minimizer, sampled-weight restriction,
RA06 sampler failure, generic-position axiom or finite test replaces any
approved support theorem.

README and metadata explicitly say the complete Target remains unproved,
canonical status stays Solved, all-exponent rate upper/lower arguments and
arbitrary-coreset additive impossibility remain absent, and isolated Linux
verification is pending. `whole_problem_verified` is false. None of
Classification, NegativeAnswer or Target is advertised as a proved theorem or
selected as a completed Comparator result. The preserved Target definitions
and their statement-trust checks are not counted among the eleven proofs.

## Independent combined replay

I invoked the inspected read-only `reproduce.py` separately with official Lean
4.33.1 and the pinned package cache, retaining results under
`package-review-inventory/replay/`. All eleven commands passed, including the
three declared default targets Solution, SupportAudit and Identity, the frozen
Reviewed boundary and the separate Challenge. The ten materialized dependency
repositories matched their manifest revisions and had no tracked changes both
before and after replay. The runner removed temporary compiled outputs and
left the stage untouched.

All eleven LeanCert kernel assertions passed, and all eleven transitive axiom
reports contain exactly `propext`, `Classical.choice` and `Quot.sound`. The
independent replay result SHA-256 is
`a9e19fa2d193f670511bd393f139e3bd21fabf72fb5bc031c07e7eb5c30a7816`.
The unchanged published metadata validator also passed:
`Manifest schema and comparator coverage: PASS (11 declarations)`.

Reproduce the source replay and structural review with:

```bash
python3 /private/tmp/nla-ra05-oct23-package/reproduce.py \
  --lean /private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean \
  --packages /Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages \
  --output /absolute/new/output-directory
python3 reviews/2026-10-23-solved-lean/package-review-inventory/review_package.py \
  /private/tmp/nla-ra05-oct23-package
```

This is local arm64 macOS source elaboration and kernel-trust evidence using
shared compiled dependency caches. It is not a fresh dependency rebuild, raw
kernel replay, actual Linux sandboxed Comparator result, CI receipt or proof
of the full RA-05 problem. Subsequent isolated Linux acceptance can certify
these eleven support exports at its exact committed inputs while RA-05 remains
Solved. No numerical certificate or external human endorsement is claimed.
