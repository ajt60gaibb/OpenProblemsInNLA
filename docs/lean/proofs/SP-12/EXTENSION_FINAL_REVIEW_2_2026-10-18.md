# SP-12 independent extension, final assembly and package review 2

Reviewer: OpenAI Codex AI agent `/root/solved_inventory`, 18 October 2026.
**APPROVE the five other-author sources at the hashes below and the exact
canonical export/package fidelity. No blockers found.** I did not author or edit
SAPTestSpace, ExtendedRows, NeighborhoodLifting, VertexExtension or Final. I did
author Chromatic, Critical, ChromaticInduction and GramDifferential, so this is
explicitly not independent approval of those own modules. Their complementary
root, fr05 and verification reviews are separate required evidence.

| Independently reviewed source | SHA-256 |
| --- | --- |
| `SAPTestSpace.lean` | `175ab79714c2768de77fa195443c9ab6b084b95800772341f7d20b7e00c7d1c8` |
| `ExtendedRows.lean` | `1294004dbc23d569595207243c4a941c057a5156db4c703a44ea589b23938e2c` |
| `NeighborhoodLifting.lean` | `26bd77032db9a61803aa6fa483cf6b080341c627bc61ac321ea9542f895c7722` |
| `VertexExtension.lean` | `648476c3e983193de5678507fd2227e2d6f7b268079e454e4f5e063bf89adadd` |
| `Final.lean` | `df9812c527efabaf60a12ecccc7ed33fe1c69bc0e3a399a7cb28030ddf59e61d` |

I read each complete actual source, traced its relevant imported meanings and
freshly compiled its unchanged bytes. All five passed with LeanCert kernel
assertions and only `propext`, `Classical.choice`, `Quot.sound` in the printed
closures. Exact commands, platform, source/log hashes and raw logs are in
[extension-final-review-2-evidence-2026-10-18/result.json](extension-final-review-2-evidence-2026-10-18/result.json).
These direct local checks use pinned cached dependency/prerequisite objects;
they are not the separate isolated full-closure replay or a Linux Comparator
receipt. The verification agent owns that fresh complete replay.

## Fixed test space and actual extended Gram factor

SAPTestSpace uses exactly the real symmetric matrices with zero diagonal and
zero entries on graph edges. It does not replace SAP by an arbitrary supplied
invariant. Its multiplication map is the actual A*X. The equivalence with the
frozen StrongArnold definition requires the exact HasPattern premise and uses
both directions correctly: nonedges force A entries to zero, while edges force
X entries to zero. Ordinary and Hadamard multiplication remain distinct.

The openness theorem concerns injectivity on the *fixed graph test space*, even
at multiplying matrices with a different pattern. This distinction is necessary:
the block-diagonal base has not yet made the new edges nonzero. The source proves
continuity of the actual finite-dimensional multiplication family and applies the
existing open-injectivity theorem. It does not assume SAP openness on a moving or
undefined test space.

ExtendedRows constructs the actual rows in dimension d+1. The new row is the
first coordinate vector; each old row is its old d coordinates with one added
coordinate b_i. All four Gram block identities are proved, including the old
block b_i*b_j+gram(R)_ij. Continuity is proved entrywise in the ordinary finite
product topology. At b=0, multiplication's first row forces the test matrix's
first row to vanish. Symmetry forces its first column to vanish; the old SAP
kills the remaining block. This covers h=0 and d=0 and makes no unjustified rank
constancy assumption.

## Local image and one-vertex extension

NeighborhoodLifting turns the proved map-of-neighborhood equality into an actual
preimage in the chosen good neighborhood. It applies the product map with the
identity on the added coordinates. The image of a neighborhood is a neighborhood
under the exact map equality; pulling it back along the target path yields a
real ball about zero. Choosing its positive half-radius supplies an actually
nonzero parameter. No continuous preimage selection, hidden parameter oracle,
choice of a favorable factor branch or unproved implicit-function conclusion
appears in this helper.

VertexExtension uses the exact unordered old nonedges, not a subset of unwanted
zeros. The target coordinates are minus the actual b_i*b_j terms. Equality of
that coordinate map implies the required correction for every ordered old
nonedge, by the proved symmetry and scalar commutativity. The chosen good
neighborhood simultaneously retains fixed-space multiplication injectivity and
all old edge nonzeros. Both properties are proved to hold at the actual base and
persist by continuity and finite intersection.

The added coordinates are epsilon precisely at new edges and zero precisely at
new nonedges; epsilon is nonzero. The resulting actual extended factor therefore
has every required new edge nonzero, every new nonedge zero, all old nonedges
cancelled exactly, and all old edges retained nonzero. The final exact pattern
then converts the retained fixed-space injectivity into the frozen SAP.
Dimension increases by exactly one, with no claim that row rank is constant;
the final Gram rank inequality is sufficient for the nullity argument. Empty
old graphs, zero-dimensional old factors, isolated added vertices, arbitrary
edge signs and disconnected graphs are included.

The local surjectivity lemma used here has actual HasPattern and StrongArnold
premises, both supplied by the old witness. I wrote its separate proof module,
so its independent source approval is deliberately delegated to other agents.
This review confirms the other author's extension uses precisely those proved
premises and no stronger oracle.

## Final exact Target and canonical package

Final exports `NLA.Proofs.SP12.target : NLA.Statements.SP12.Target` with no
residual argument. It instantiates both constructive inputs of the discrete
induction with the actual exists_strongDelta_gram and exists_vertexExtension
theorems. The earlier conditional reduction is not exported as an unconditional
proof without those inputs. No literature theorem, arbitrary realization,
analytic-surjectivity hypothesis or chromatic oracle survives in the full type.

I also freshly compiled the actual canonical Solution source against the checked
byte-identical shared prerequisite objects. Its full export passed the kernel
assertion with exactly the standard three axioms; the actual command/log is in
[canonical-wrapper-build.json](extension-final-review-2-evidence-2026-10-18/canonical-wrapper-build.json).
This is not a separate isolated canonical closure rebuild.

The canonical Solution is a direct wrapper of that complete theorem, exporting
exactly `NLA.SP12.target`, and applies kernel trust/axiom checks to that export.
The type is unchanged from the independent preproof approvals: every n>0 and
every simple graph on Fin n, exact real symmetric off-diagonal pattern,
nonnegative quadratic form on every real vector, all three exact SAP equations,
and nullity at least the natural proper-coloring infimum minus one. The diagonal
is otherwise free. Isolated, disconnected and singleton cases are preserved.
The final source does not strengthen the target's hypotheses to critical graphs
or positive minimum degree. Complementary reviews cover my discrete induction
and the real-LSS/StrongDelta construction; I do not self-approve those proofs.

I checked all 51 lock copies against both their shared sources and actual
canonical bytes, and checked the selected exports/configuration hashes. All
matched. That is 36 SP-11 proof modules, 12 SP-12 proof modules, and three
statement/infrastructure modules. The canonical ORIGINAL is still identical to
the unchanged canonical README. The live/frozen SP12 and numerical specification
hashes still match the preproof boundary. The Comparator selects only the full
NLA.SP12.target, permits only the three foundational axioms and has no definition
holes. The direct dependencies/toolchain remain the exact reviewed pins. The
v0.4 schema and selected-result coverage validation passed for one declaration.
Actual package/copy/config/document checks are recorded in
[package-audit.json](extension-final-review-2-evidence-2026-10-18/package-audit.json).

Canonical Solution SHA-256 is
`d09d569d4e099c60ed12fb9a896f551dceb86f1f3685dff391395c5be6bd0369`; Challenge is
`cd63c947c028b797e2ec3a9b82807d1a89d81b1283b25d6c814643a278480941`.
The complete local package under review has these document hashes:

| Document | SHA-256 |
| --- | --- |
| `README.md` | `02c96901e5ca6f13e5e29d4dd3879f8404fb209ed46772c5d8cddbb2c606f93c` |
| `formalization.yaml` | `0570926a56f1fb52f157fac3f8fec26bc479a19d0ebe0959447f0b0784622c4b` |
| `proof-source-lock.json` | `7dc8172301ccba0a2df4c2161b87267f8579e21108bd24642faa499eb8727410` |

Metadata correctly keeps whole_problem_verified false and canonical_status
Solved while the actual SP-12 Linux Comparator run is pending. Its source-complete
phase is distinguished from authoritative verification in its status/result text.
README correctly separates local proof/kernel checks, the SP-11 prerequisite
receipt, and the still-required SP-12 committed-project run. I inspected the
retained complete SP-11 receipt and its referenced independent review report; I
did not rerun that artifact audit. The prerequisite acceptance claim is
separately sourced and is not used to infer SP-12 acceptance.

Attribution remains Hall for the mathematical theorem/construction, Stepaniants
for the explanatory application note, and AI agents for formalization/review.
The Gram-factor and finite-deletion implementation adapt the source's argument
without assuming a fixed-rank manifold or continuous right inverse. There is no
human peer-review or source-author participation claim. Permanent ID, canonical
path, original target, original snapshots and other catalog pages are unchanged.

This approval is sufficient to proceed to the actual canonical Linux gate with
the complementary independent proof reviews. It does not itself promote SP-12
or claim a Linux Comparator run that has not occurred. If the committed source
bytes change, refresh the relevant review and mechanical evidence.
