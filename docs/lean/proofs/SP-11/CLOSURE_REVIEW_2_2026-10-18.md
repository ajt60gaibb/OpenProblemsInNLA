# SP-11 complete shared target — second independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I did not implement `Final.lean`, `DiagonalUniqueness.lean`,
`TopOccurrences.lean`, or `EdgeUniqueness.lean`. **Verdict: approve the complete
shared frozen-target proof at the source hashes below, with local kernel
evidence.** Canonical-package and Linux verification are separate next steps.

| Module | SHA-256 |
| --- | --- |
| `Final` | `de7bfb35944fb25d0d7b8a15b7f7331fa942922b79a6af79e4c285dfa071840a` |
| `DiagonalUniqueness` | `e5ccc886ef054e7d4e39a45a867b2621a5e973836aa0979744919aa30dea3385` |
| `TopOccurrences` | `5b7109a544fe220f43363c23ac7b23b5cee0f57d3f1aaa6e4c42cf379930f133` |
| `EdgeUniqueness` | `7ba36de0cfcf652fbd1537a52979d2f7345be68d60aabfa9283a04cec2aa46db` |

The exported theorem `NLA.Proofs.SP11.target` has the literal unchanged type
`NLA.Statements.SP11.Target`, with no additional parameters. This is every
positive-order finite simple graph, with an unrestricted real symmetric matrix,
exact off-diagonal edge/nonzero equivalence and minimum-degree nullity bound.
The shared frozen statement hash remains
`7de112a24cb0b78894d495b840a77a58572cce574d5d77eda15381410c65b131`.

`polynomialLSS_nonzero_ordered` uses the genuinely nonzero canonical sign and
the actual paired-garden coefficient formula. Equal root labels use the
proved diagonal uniqueness theorem. Distinct ordered edge labels use the
proved edge uniqueness theorem. In both cases the selected coefficient is
nonzero, so the actual Gram polynomial is nonzero. Zero-sign summands may
share the exponent and contribute zero, as accounted for by the coefficient
bridge. No remaining noncancellation hypothesis is supplied by the caller.

`polynomialLSS_nonzero` handles arbitrary root order by exact symmetry of the
Gram sum over the commutative real polynomial ring and undirected adjacency.
The final theorem invokes the previously reviewed greedy relabeling reduction:
an actual permutation supplies an ordered greedy graph and valid arities;
one real specialization preserves every required Gram entry; the Gram rank
bound and dimension inequality imply the requested nullity bound; exact
pattern, rank and minimum degree transport back through the same permutation.
The final export therefore closes the original target, rather than a supplied
conditional representation theorem.

The diagonal and edge source reviews are detailed in the campaign reports
`SP11-DIAGONAL-UNIQUENESS-INDEPENDENT-REVIEW.md` and
`SP11-EDGE-UNIQUENESS-INDEPENDENT-REVIEW.md`. They retain repeated vertex
occurrences and shared `Sigma vertex CoordinateSubset` variables. The edge
proof uses the inserted earlier root among the later root's actual children
to provide every smaller-color blocker; adjacency supplies strict label order.
All other occurrences have actual parents and ordinary earlier siblings.

An immutable fresh-source build passed **39 Lean commands**: all 36 proof
modules in the closure, two unchanged statement/infrastructure modules and a
separate consumer. All **289 explicit named declarations**, including **199
theorem/lemma constants**, passed theorem-kind checks where appropriate,
LeanCert kernel trust and transitive axiom checks. The consumer additionally
requires the final constant's type to be the literal frozen Target and checks
its kernel trust again. Its axioms are exactly `propext`, `Classical.choice`,
and `Quot.sound`. Every frozen source was unchanged after execution; all ten
dependency pins and tracked-source cleanliness checks passed before and after.

```bash
python3 docs/lean/campaign-2026-10-17/verification/check-sp11-tree-color-support.py \
  --evidence-name sp11-full-target-review --top Final \
  --target-theorem NLA.Proofs.SP11.target
```

Exact snapshots, generated consumer, compiler/driver identities, raw logs and
machine-readable results are in `sp11-full-target-review/`. Its explicit
profile records `full_sp11_target_proved: true` for local kernel verification
and `authoritative_linux_comparator: false`. The earlier successful generic
profile with support-era metadata is retained separately in
`sp11-full-target-initial-profile/`; the full run was repeated with the new
literal-target assertion rather than relabeling that old result.

I implemented five transitive support modules (`MonomialProducts`,
`PriorListStructure`, `LSSLabelBounds`, `PriorInsertion`, `AugmentedColors`).
They have fresh runtime evidence here and independent source reviews by the
other agents. I do not claim self-review as independent review of those files.
All remaining closure modules have source-specific independent campaign
reviews. This is AI-agent review and local macOS Lean elaboration/LeanCert
kernel-trust evidence using pinned cached dependencies. It is not external
human peer review or a Linux Comparator receipt.
