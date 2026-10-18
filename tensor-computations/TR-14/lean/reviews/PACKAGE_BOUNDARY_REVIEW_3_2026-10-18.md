# TR-14 exact canonical boundary — independent pre-Solution approval

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I authored neither the TR-14 statement definitions nor the canonical scaffold.
**APPROVE this exact frozen full boundary before Solution is written.** No Solution existed during either this review or the retained fresh boundary audit. This is not a Target proof or Linux acceptance claim.

The selected theorem is `NLA.TR14.target : NLA.Statements.TR14.Target`. For every m≥3, n≥2, every complex moment vector of length m(n−1)+1 and every natural width r, the actual ordinary and symmetric width predicates are equivalent. Ordinary factors can depend independently on mode; symmetric factors use one common vector per term with an unrestricted complex coefficient. Products are complex bilinear products with no conjugation or normalization. Empty sums at r=0 give the zero tensor. The zero and every exceptional moment vector are included. There is no genericity, Vandermonde, nonzero-input, squarefree-apolar, chosen-chart, minimal-width or supplied-rank-formula assumption in Target.

The zero-based Hankel index is the sum of the m input indices, exactly equal to the source's one-based sum minus m; its finite bound is m(n−1). The all-width formulation is precisely the equality of least exact decomposition lengths: zero padding turns each attainable width into all larger widths, symmetric weights can be absorbed into one ordinary mode since m≥3, and finite Hankel symmetric decompositions exist over the infinite complex field by ordinary finite Vandermonde interpolation. Thus it neither adds a new quantitative rank formula nor restricts witnesses to Vandermonde vectors. Such vectors can be used to construct witnesses, but are not part of the boundary definition.

The seven source-lock copies match both their recorded SHA-256 and exact shared source bytes: live TR14, Infrastructure, separately frozen Reviewed.TR14, ORIGINAL, numerical specification, license and toolchain. ORIGINAL is byte-identical to the retained canonical README; permanent registry ID TR-14 still maps to tensor-computations/TR-14/README.md. Sidney Holden's mathematical credit, prior Nie–Ye/Qi source credit, source history and all original target text remain unchanged.

| Core input | SHA-256 |
| --- | --- |
| `boundary-source-lock.json` | `f9b3a2ac61aa2b257be127a6983adecb9e5d2e72b9f6df8ce092eba2952b6ab5` |
| `NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| `Reviewed/TR14.lean` | `9990f933adf8a8593f6a1fcc70aeeaeed8abdfe05e7738bd5b538e719ad9c356` |
| `Challenge.lean` | `3f443cdd0a9716f87069ce9aae3b28957fe442878aa034dc7468b815b539d1ad` |
| `Identity.lean` | `bb3dea1091354721337f9ffa7e8b8f0f3d8de8bdf51dc91777bf61ca5afd48ea` |
| `comparator.json` | `cae9bd8a4ed53f9a8349b966e32636a1429f1ec4dc680bcaaec1f8e5d9036bbb` |

Identity proves live/frozen Target equality by `rfl`. Challenge imports only the actual statement and contains exactly the intentional comparison placeholder. Comparator selects only NLA.TR14.target from Solution, permits no replaceable definitions, and permits exactly propext, Classical.choice, Quot.sound. The ordinary pinned Lean4.33.1/Mathlib/LeanCert profile remains unchanged; resolved dependency source identities match the shared project.

A separate fresh-output audit passed **15 source-lock/configuration/pin checks**, six positive Lean commands and the expected seventh negative command. It freshly compiled actual copied Infrastructure, live TR14, Reviewed.TR14, Challenge and Identity, then an independent consumer checking the selected theorem kind and literal frozen Target type, and Identity's kernel trust/axioms. A separate kernel assertion on Challenge's target fails as required for sorryAx, confirming the placeholder cannot count as a proof. The source copies remained unchanged through the audit. Pinned dependency objects are reused; no campaign project objects are imported.

Exact original source snapshots, compiler/dependency identities, consumer and raw logs are retained in [boundary-review-3-evidence/](boundary-review-3-evidence/). The exact driver is included there. Its repository invocation is `python3 docs/lean/proofs/TR-14/verification/check-canonical-boundary.py`; after the package is upgraded, its retained source snapshot can be replayed with `--snapshot docs/lean/proofs/TR-14/verification/canonical-boundary-review-3/source --evidence-name historical-boundary-review-3`. Historical pre-Solution source bytes, rather than a later Solution-bearing package, define this approval.

This independent AI-agent approval permits implementing Solution against the unchanged boundary. The complete actual proof, canonical copied closure, theorem-kind/axiom audit, semantic source review and real isolated Linux Comparator remain separate completion gates. No source-author endorsement, external human review or full Target proof is claimed. No mathematical source, original page or registry entry was edited for this review.
