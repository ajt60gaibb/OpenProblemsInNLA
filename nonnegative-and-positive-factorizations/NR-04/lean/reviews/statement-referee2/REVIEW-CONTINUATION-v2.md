# NR-04 independent statement review — amended boundary approved

Reviewer: `/root/nr04_statement_referee`, independent OpenAI Codex agent.
Phase: exact-source statement review, 19 September 2026 (UTC).

**Verdict: APPROVE THE STATEMENT BOUNDARY on the v2 bytes below.**
Both findings in the preserved provisional `REVIEW.md` are resolved. This is
one independent statement approval, not a proof review, mathematical theorem
certificate, whole-problem verification, or publication approval. Root's
second independent statement review is a separate gate. No proof work was
performed by this reviewer.

## Bound approved files

Packet: `.local-recovery-20260918/development/NR04-statements-v2`.

| File | SHA-256 |
| --- | --- |
| `NLA/NR04/Definitions.lean` | `d980b0515c5d91c3a1d0c1863974378e78fd7775efeab4dc835fc6e93cbe276c` |
| `Challenge.lean` | `42eaddcff4ce84b263fc6530a01e3a43d492c11360917fa0242ebfee7f9210b4` |
| `NUMERICAL_TARGETS.md` | `5a758137ec0e9350283e66b5462ca12cf3f2fde1cd58b92ed88b1d668a0aa3cd` |
| `comparator.json` | `23fffe05b309033b5d7bd9cfad8b6ff9551433a4bd6fb92564b763e67c282e8b` |
| `formalization.yaml` | `ba04b401de77c7bdefe5df4ba49271cafc8d3a0501e160b84be22776afbf0ae8` |

The full input-file manifest is in `AUDIT-v2.json`, and the approval record
binds it in `MANIFEST.json`. The original v1 packet and provisional report
remain unchanged. Approval does not apply retroactively to v1's failed
elaboration or malformed YAML.

## Resolution of earlier findings

**F01 resolved.** I read the entire v1-to-v2 diff and amendment record and
independently checked exact text equality after removing only the new
`Mathlib.Data.Real.Basic` import and `set_option autoImplicit false` lines.
There is no mathematical header, definition body, domain, or quantifier
change. Both files now prohibit undeclared automatic implicit variables.

I inspected root's actual successful `recovery-030` receipt and both full
NR-04 logs. Definitions compiled freshly with exit code zero in 2.26 seconds,
on the approved `d980b...` source. Its output was then the exact dependency
of the fresh 2.33-second Challenge run on the approved `42eadd...` source.
The latter was staged under the filename/module `NR04Challenge`; its bytes
are identical to the packet's `Challenge.lean`. All 15 deliberate `sorry`
warnings are present and expected. They prove no mathematics.

The receipt's SHA-256 is
`7f0c53d32ceeca6c5fceea157793e18f2f7afba41ca97d46a5b21ecd9cf7db70`.
The Definitions log is empty, SHA-256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The Challenge log's SHA-256 is
`8e8c28e03f98950821cfd8513e1afd1e534a6405bf380468a49373069f64be0c`.
`HEADER-EVIDENCE-v2.json` retains the exact commands, sources, output hashes,
dependencies, and inspection checks. The commands are root's actual local
macOS Lean runs with one thread and a 4096 MiB limit; I did not run another
compiler. This is not a GitHub or Comparator result.

**F02 resolved.** The numerical-certificate value is now a folded YAML
scalar. I independently ran Ruby `YAML.safe_load` and Python
`jsonschema.validate` against the exact retained v0.4 schema. Both passed.
The actual commands, outputs, schema hash, and results are in `AUDIT-v2.json`
and its stdout/stderr files. The amended metadata also records the rejected
first header attempt instead of erasing it. Its statement-elaboration field
is the dated pre-run snapshot; the actual subsequent header evidence is
attached here and must be reflected in live metadata at final packaging.

## Full semantic scope of approval

This continuation incorporates the complete all-15-contract review,
canonical/manuscript comparison, adversarial geometry checks, library
definition inspection, numerical minimization, and attribution analysis in
`REVIEW.md`. Those mathematical source bytes and intended contracts are
unchanged. There is no outstanding semantic finding.

In particular, the final statements still concern arbitrary real factors,
all natural widths below seven, exact matrix multiplication, and the genuine
least-width definition of nonnegative rank. Normalization is intermediate
work to prove, not a constraint on the original factors. The two geometric
statements still require actual finite extreme-point sets, include
degenerate sections and repeated generators, and do not assume either the
polygon-contact conclusion or a three-polytope facet bound. The full lower
bound remains an unproved obligation of the future Solution. The explicit
width-six impossibility answers the unchanged original canonical target.

Comparator still lists all 15 exact theorem names, no definition holes, and
only the three standard allowed axioms. Future Solution must remain
independent of Challenge. Actual proof checking, consumed kernel-mode
LeanCert certification, final proof reviews, and real non-root Linux
Comparator/kernel/sandbox checks have not occurred for NR-04. A successful
header run does not discharge any of those gates.

No complete verified-target count is increased. The challenging polygon and
polytope prerequisites remain substantial future formalization work.
