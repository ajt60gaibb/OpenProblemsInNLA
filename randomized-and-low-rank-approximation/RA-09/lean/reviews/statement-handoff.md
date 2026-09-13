# RA-09 frozen statement handoff

**Ready for two independent statement referees; no proof implementation.**

Project: `randomized-and-low-rank-approximation/RA-09/lean` in isolated worktree `/tmp/nla-lean-ra09-worktree`, branch `codex/lean-ra09-concave-frobenius-transfer`, unchanged base `5830ed4fb06da0659414a3deb2a40ad327aca052`. The initial tracked source-only worktree is clean; every new project file is untracked and no dependency/cache was copied. Canonical status remains **Solved**.

`reviews/statement-freeze.json` SHA256 **c144b68990fca06c554790b25bfaef7544c0a8baf532e5b38365fe74ee9c87ed** binds **31 project files and 17 original Git source/policy files** (13 mathematical/source records and four repository policies). The JSON maps paths directly to SHA256 strings and separately records actual Git blob IDs. It excludes only its own exact path and this later handoff, plus explicitly listed generated file classes. All source/policy inputs equal the fixed Git base byte for byte.

| Boundary | SHA256 |
| --- | --- |
| `NLA/RA09/Definitions.lean` | `2a9b0d9d536bc2620fbe3814ed95640caeae8a49e8b13a9e2136b469ba09ece9` |
| `Challenge.lean` | `5b275a09558f3b03b67b4ef0c7764db854d9c516190f05135a426c14eb7b1e6e` |
| `NUMERICAL_TARGETS.md` | `638e5a3c5c87bc284eee127ac11dde58fba9d9c705e40669efcd1dcb91ed52ee` |
| `SourceCorrespondence.md` | `142f0b485aa77978ab89def0263b6456e30b660235ae635af99409c19038821a` |
| `comparator.json` | `dc16c0577badd3cefa27669c7efd3bdf525a21e5f45516e8b1f2d32158cca6cd` |

There are **17 complete grouped contracts**, all intentionally unproved in Challenge. The final contract is the exact original all-dimension/all-function/all-eigenbasis affirmative target under the original trace-deficit premise. Actual Frobenius norm, CFC, PSD order, spectral existence, all selected bases, unbounded scalar/harmonic/overlap bounds, `f(0)>0`, `f(tau)=0`, and zero-tail closure all remain explicit obligations. No function class, premise or norm has been substituted. The source's unnecessary unordered/sharpness results and larger function class are outside the advertised exports.

The numerical statement plan was written before any proof. The exact universal scalar factors admit a sum-of-squares argument and require no interval computation. Root explicitly accepted LeanCert kernel trust/dependency auditing for this pure exact scope, with no artificial numerical singleton. The independent feasibility note and RA-08 statement-definition design snapshot are retained with attribution; neither imports an RA-08 implementation or an admitted theorem.

Fresh local statement validation passed all three commands in `reviews/statement-evidence/attempt-f944v7r9`: Definitions (13.83 s), Challenge (3.56 s), and actual-instance/API inspection (5.77 s). Only the 17 intentional Challenge warnings occurred. All 17 structural LeanCert kernel/axiom inspections used exactly the standard three. The actual elaborated norm is `Matrix.frobeniusNormedAddCommGroup`; the actual CFC is Mathlib's `cfc` with matrix topology; actual PSD order is positivity of the difference. All ten exact dependency Git pins were clean before and after. Project objects were elaborated in a fresh separate prefix using matching MI-22 dependency objects read-only, with all old project object directories excluded. No Linux or complete-proof claim follows from these statement checks.

Supplementary exact diagnostics independently expanded the SOS and all three cleared-denominator source identities, checked 500 rational scalar instances and a noncommuting three-by-three matrix example, and verified the zero-tail positive-intercept example with different null-space basis selections. Those transformed truncations actually differ while both exact errors equal `(n−k)f(0)²=1`. These diagnostics test the design; they do not prove the universal assertions.

- Input audit SHA256: `a1e7cbda999685db3816e199fef384bc6c3b8f685aa20ca41b72dff27396da73`.
- Exact reconstruction SHA256: `5250865feb897552ae9be7879b61458193e434a34096c044e0c876f620cae48a`.
- Comparator: all 17 exact names, no definition exceptions, only `propext`, `Classical.choice`, `Quot.sound`.
- Required independent statement referees: `/root` and `/root/formal_review_standards`; neither approval exists at this freeze.

Mathematical theorem: **Matthew J. Colbrook**. Formalization: **George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA**, AI-assisted, no contact email. Original Persson–Meyer–Musco credit and source attribution are preserved. No formalization manifest, implementation, publication change, commit or push has been made. Two exact independent statement approvals and explicit coordinator authorization remain required before proof implementation.
