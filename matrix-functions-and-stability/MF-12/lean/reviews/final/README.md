# MF-12 independent final referees

Both independent AI-agent referees accepted the complete mathematical source and
the actual canonical run 35037011332 at immutable proof commit
3d06c49635bbdde109c491510641204285eaf05c:

- [Elimination referee](referee-elimination/REVIEW.md), with the complete prior
  mathematical review chain and a fresh source/runtime reconciliation.
- [Inequalities referee](referee-inequalities/REVIEW.md), with an independent
  full mathematical review and separate actual-evidence reconciliation.

Neither agent authored MF-12 mathematical implementation. The elimination referee
also prepared publication metadata and evidence; that changes no proof source.
The reports are AI-agent reviews under the repository's scoped Tau Ceti protocol,
not external human peer review or official certification.

Every original review file is retained byte-exactly. Historical Lean snapshots
are stored as .lean.txt; the [path map](../../verification/publication-2026-09-15/REFEREE-PATH-MAP.json)
records original and retained names. Restore those names when inspecting the
original scripts' relative-path assumptions. The reviewed canonical files and
all actual final proofs remain in their normal active project paths.
