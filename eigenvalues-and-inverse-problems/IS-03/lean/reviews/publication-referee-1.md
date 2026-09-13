# IS-03 independent publication review

**Verdict: APPROVE the corrected, sealed publication state.** The two editorial
scope omissions described below were corrected and independently checked. No
mathematical, configuration, proof, canonical-target or PDF correction is
requested. This review authorizes no automatic commit or publication.

Reviewer: `/root/leancert_examples`. I authored neither the IS-03 statements,
proof nor publication preparation. I previously served as independent statement
and final mathematical referee 1 and as the independent operational reviewer.
This additional editorial/operational review is **not another mathematical
referee**. Root and `/root/solved_statement_inventory` coauthored the mathematics;
`/root/formal_review_standards`, the other independent mathematical referee,
prepared the publication. Root made the bounded wording correction. The review
claims neither external human review nor official Tau Ceti endorsement.

## Exact state and resolved finding

The reviewed integration is `ab164900f806ab7208ca8b0107a6238603eaacad`, incorporating
upstream `5830ed4fb06da0659414a3deb2a40ad327aca052`. The actual verified candidate
is `f87375fa5d7926fe0e065199eaab8f15ac5a5e48`, Ubuntu run **34728101436**.

I read the initial publication handoff and full diff. Two standalone descriptions
in `formalization.yaml` and the new IS-03 RESOLVED paragraph omitted the
**entrywise-nonnegative** qualifier from the excluded realization. The theorem
does not exclude arbitrary real companion realizations. Root corrected exactly
those two strings, preserving the initial evidence and exact before/after
snapshots in a separate correction package. I compared the replacements byte
for byte, checked all new hashes and the three actual successful correction
checks, and re-read both corrected descriptions. This is a resolved publication
finding, not a change to the mathematical result.

The following seals are jointly part of this approval:

| Record | SHA-256 |
| --- | --- |
| Initial publication handoff | `56f6ef7249a2e364117ed1a576c0c341791460ae9090def5557aca57addb53d8` |
| Initial publication integrity checks | `8c2123242a0c56ccc78943c8b5cbfd21095d2ef0c2e6877bf8e69c220ac51d26` |
| Initial publication outer manifest, 35 bound files | `f01c38486feff1079f6366dd22e2b39437453d1b3040e102f1318876b1133b97` |
| Supplementary scope correction | `10a2d7e8557e656ccd5472131e51d90000505a8fd77bf9e7f7cc33a3616c49ae` |
| Correction outer manifest, 10 bound files | `4b996130f6e42faa97e7960b9041d0f7a026e64cb4c71bdef66047eb6d2044ca` |
| Corrected `formalization.yaml` | `d9fc291e9689d92fda9c96ad9f3033d081583a89818802b77143f9869e007b0f` |
| Corrected `RESOLVED.md` | `a7bb696b250fc2f4742dcd442d6e38617f6d835a9509759901112b6bc94dca81` |
| Final canonical PDF | `48be4ca94c0582e6758dac5a96307f0cac8a9369a64b2c305165a2273e1d5cdc` |
| Final canonical TeX | `74d890e50b88c14201ca3d685357b7d3fbce8e4121c3e8402b34a2a64fb2462b` |

## Mathematical correspondence and public scope

I re-read the complete canonical entry, full Lean README, actual manifest,
IS-03 RESOLVED subsection and all three final PDF pages. The original problem
statement and reference/audit suffix are byte-identical to upstream. The full
claim retains every `n ≥ 5`, every real entrywise-nonnegative matrix of order
`n`, the actual normalized characteristic-polynomial derivative and a real
entrywise-nonnegative realization of exactly order `n - 1`. No symmetry,
diagonalizability, trace, irreducibility or simple-spectrum premise is added.

The public seven-export table matches the actual Comparator selection. The
arbitrary-real-matrix trace theorem, whose only premise is characteristic-
polynomial equality, is distinguished from the final exclusion of nonnegative
realizations. The unchanged `diag(1/2,C₂,C₄)` witness, exact seventh trace
`-8593/823543`, derived eigenbasis and multiplicity-aware Newton bridge are
described faithfully. The actual retained kernel LeanCert scalar certificate
is consumed in the contradiction. Zero padding, Monov's separate consequence,
minimal order and priority are explicitly outside these exports.

Matthew J. Colbrook retains mathematical authorship. George Stepaniants receives
formalization credit with the approved **Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA**
affiliation and AI assistance disclosure, without a contact email. Source,
implementation, referee, infrastructure, operational and publication roles are
distinguished. The preservation of historical pending notices is explained.

## Evidence and preservation checks

My separate read-only auditor checked these identities against actual current
bytes, immutable Git blobs and retained execution receipts:

- All **303 candidate inputs**: 301 nonwrapper files unchanged, with both exact
  executed wrappers preserved in the publication archives. All **203 proof**
  inputs and **34 statement** inputs remain available unchanged, using the
  exact historical README archive where appropriate. All **10 original source
  snapshots** match candidate Git blobs; the regenerated canonical README/TeX
  are correctly distinguished from their retained original snapshots.
- All **452 operational files** unchanged: 445 Linux files, including their
  outer manifest, and seven root-acceptance files. I rehashed complete inventories,
  including every nested manifest. Both prior statement and both final proof
  evidence inventories retain their respective 23, 26, 36 and 45 files.
- The current manifest differs from the executed one in **exactly five fields**:
  `status.scope`, `review.status`, `review.notes`,
  `review.linux_verification.status`, and `review.linux_verification.note`.
  All seven exports, source references, Comparator configuration, empty
  definition exceptions, pins and standard-three axiom declarations are unchanged.
- All **217 permanent IDs** and paths unchanged, **216 other canonical entries**
  unchanged, all **16 previously verified entries** preserved, and **6967 other
  upstream files** unchanged. Only the existing IS-03 RESOLVED subsection changes;
  the surrounding shared source group and every other subsection are identical.
- Exactly nine tracked publication files change. Generated catalogs only promote
  IS-03 and change the evidence totals from 16 to **17 Lean verified** and 76 to
  **75 Solved**. Counts remain **53 Open**, **72 Partially resolved** and 217 total.
- I read and checked hashes/exit codes of the nine original actual preparation
  checks, including both ID validators, schema/full-export coverage, 17 ID tests,
  formatting, catalog regeneration and PDF rendering. The correction's three
  fresh schema, formatting and diff-whitespace checks also passed. I did not
  rerun a source build, renderer or test suite in this publication review.

The Linux descriptions accurately attribute success to the immutable candidate,
not these later metadata bytes. They retain all seven matched exports, eighteen
standard-three axiom reports, actual default-kernel replay and both real control
suites, ten freshly pinned dependencies and the observed 8690 official Mathlib
cache artifacts. The 1718/3101 graph counts do not claim a full source rebuild.
Nested Bubblewrap's UID-map denial is described as occurring before the inner
write. The separately computed digest of the complete 152-file run-log ZIP is
not called a GitHub-published digest. Root operational acceptance is explicitly
not an independent mathematical review. My earlier operational evidence and
root's separate acceptance are both bound by the unchanged inventories.

## Visual inspection and local review limits

I viewed every final PNG at original detail. Page 1 contains attribution and the
verified scope; page 2 contains the actual verification and complete original
target; page 3 preserves references and dated historical status checks. All
mathematics, text, links, margins and footers are readable; no overlap, clipping,
missing glyph or layout correction was found. The exact PDF, TeX and all three
page-image hashes are in `publication-referee-1-evidence/VISUAL-REVIEW.json`.
The wording correction did not change these bytes, so no new PDF was necessary.

An initial attempt to write this review's small JSON output encountered local
`ENOSPC`; no content failure or source mutation occurred. Root cleared disposable
inactive compiled artifacts, preserving all source and evidence, and the same
read-only checks were resumed. This environmental interruption and the final
command result are retained in the separate review evidence. No Lean, dependency
download, cache copy, mathematical proof, canonical edit, commit or push was
performed by this publication review.

The adjacent evidence manifest binds this report and every evidence file,
excluding only that precise outer manifest itself. The initial preparer and
correction seals remain immutable. Final publication remains under the root
coordinator's control.
