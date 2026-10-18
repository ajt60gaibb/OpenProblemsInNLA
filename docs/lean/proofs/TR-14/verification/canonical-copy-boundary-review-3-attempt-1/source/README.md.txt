# TR-14: complete exact-rank equality for complex Hankel tensors

[Solution.lean](Solution.lean) exports precisely `NLA.TR14.target :
NLA.Statements.TR14.Target`. The shared full theorem compiles with LeanCert
kernel trust and only `propext`, `Classical.choice` and `Quot.sound`. Independent
full-closure and canonical package audits are in progress. Actual isolated
Linux Comparator verification is pending; the canonical problem remains Solved.

The unchanged target quantifies every m >= 3, n >= 2, every complex moment
vector of length m*(n-1)+1 and every natural width, including zero. Ordinary
factors may depend independently on the mode. Symmetric factors use one repeated
vector with a complex scalar coefficient. All coordinate equalities are exact,
with no conjugation, genericity, nonzero-data or Vandermonde restriction.

For nonzero data the proof chooses an actual normalized least-apolar chart.
The same chosen polynomial supplies two actual symmetric constructions and the
unrestricted ordinary lower bound. The lower proof constructs a minimum ordinary
decomposition, independent rank-one functions, actual graph spaces and separate
graph units. A contextual product inequality, actual reduced primitive blocks,
actual polynomial image dimensions and actual whole-local-factor support counts
give the lower bound. Chart transport, choosing the smaller actual symmetric
width and zero padding prove the requested original-coordinate width. Zero data
and the symmetric-to-ordinary direction are proved directly. No rank oracle or
conditional lower-bound hypothesis remains in the exported theorem.

The canonical source closure contains 76 proof modules and two statement/
infrastructure modules. All 78 copies are byte-identical to shared sources.
Together with Reviewed, Challenge, Identity and Solution, there are 82 actual
Lean inputs. [proof-source-lock.json](proof-source-lock.json) locks those copies
and eight explicit exports. Run the repository's
[sync/check script](../../../docs/lean/proofs/TR-14/sync-canonical-proof.py)
without arguments to verify their exact identity. It does not replace Lean or
Linux Comparator verification.

[Challenge.lean](Challenge.lean) has one deliberate comparison placeholder and
imports only the statement. It is not imported by Solution. Identity checks
`rfl` equality with the separately frozen full statement. Comparator selects
only the full Target export, has no definition holes and permits only the three
standard axioms. Two independent canonical boundary approvals were recorded
before Solution existed: [review 2](reviews/PACKAGE_BOUNDARY_REVIEW_2_2026-10-18.md)
and [review 3](reviews/PACKAGE_BOUNDARY_REVIEW_3_2026-10-18.md). The only later Lake
change adds the Solution library and default build target; the earlier boundary
lock remains retained as historical evidence.

[ORIGINAL.md](ORIGINAL.md) and [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) preserve
the original source and reviewed specification, including historical phase
notices. The complete original canonical README, problem TeX/PDF and submitted
solution TeX/PDF were archived byte for byte before any status/render change at
[originals-main-36767](../../../docs/lean/proofs/TR-14/originals-main-36767/).
The permanent ID, canonical path, mathematical target and credits are preserved.

Mathematical credit remains with Sidney Holden's submitted proof, with
Beck--Lecouvey credited for the transformation lemma and Nie--Ye/Qi for the
original problem context. Formalization, source review and verification are
OpenAI Codex AI-agent work; no external human proof endorsement is claimed.

Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926` are pinned. All proof assertions use
LeanCert kernel trust. The repository's standard Linux harness independently
checks Comparator identity, the default kernel, LeanCert kernel, permitted
axioms, theorem kinds and rejection/isolation controls against committed inputs.
