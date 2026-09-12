# TR-15 local proof completion and final-review handoff

**All seven frozen Challenge exports are implemented and build successfully.**
This is the author's local verification. Two independent final proof reviews
and the real Linux kernel/Comparator workflow remain pending. The canonical
mathematical status remains `Solved`; no status, commit, push, or PR was changed.

Project: `tensor-computations/TR-15/lean` in isolated branch
`codex/lean-tr15-hankel-inheritance`, based on
`8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`.

The mathematical counterexample is Matthew J. Colbrook's. Formalization credit
is George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA. This is an
AI-assisted formalization; no human peer-review or new mathematical priority
claim is made and no personal email is added.

## Statement gate and frozen proof

Both independent statement approvals were checked and recorded in
`reviews/statement-gate.json` before any proof source existed:

| Reviewer report | SHA256 |
| --- | --- |
| `reviews/statement-referee-1.md` | `2b26253a61ababaf0d5a6a544483c72c744abbd48e48455f559764b5027a5d51` |
| `reviews/statement-referee-2.md` | `6e12a146c65d8d7037206f7eee7bdf4de0a0a1572a8a5273cc1ac14a9c65d9d9` |

The completed proof freeze is `reviews/proof-freeze.json`, SHA256
`1263937a8aeef77192d2eaf434457c36abefc77a7aefbd25fdf0dbd854ed7f6c`.
It binds 75 project files and six original canonical/manuscript source files.
The present completion report is outside that manifest to avoid a circular
hash dependency. Key immutable mathematical and configuration hashes are:

| File | SHA256 |
| --- | --- |
| `NLA/TR15/Definitions.lean` | `63b8767fd19148b269f6e4041d464f0de5dc64cac82e1448fee43115bed55379` |
| `Challenge.lean` | `6778940f8f0f645fc6be0c57f1fb8f67791e0c67c896074651bca9cada491428` |
| `NUMERICAL_TARGETS.md` | `6851bb94fb8f6049980113b4df9a1346bd3ed9549f66dd74b2b1f6a5ee947cd6` |
| `NLA/TR15/Proof.lean` | `795f3b1305dfae77fe71ec1927b7d72e9d913a2ffd0475879880f33e55c959be` |
| `Solution.lean` | `dc31d2a6a1ef891bbdc9b6781a7a250c6751d539b7cd95c4a59d08638a8faeb1` |
| `lakefile.toml` | `247a1ea746bb54d8adfb18fdce81669f85de63d5d9dfe8998eb255f54002181d` |

The approved mathematical definitions, Challenge, numerical specification,
source correspondence, Comparator configuration, and all dependency pins are
unchanged. The sole existing harness change registers `Solution` as a Lean
library and makes it the default target. The fresh-check driver reconstructs
the original TOML by reversing exactly those two changes and checks its frozen
hash. All six canonical/manuscript files remain byte-identical to their base
Git blobs; `verification/source-identity.json` records that check.

## Complete mathematical implementation

`lower_contractions` reindexes the actual finite function space
`Fin 2 → Fin 3` by `Fin 3 × Fin 3`. It expands the actual nine ordered terms
for each of the three components and proves the required polynomial identities
by exact arithmetic. No contracted coefficients or recurrence are assumed.

`upper_contraction` avoids a 64-entry expansion. For every five-tuple other
than the all-one tuple, a zero vector factor makes the product zero.
`Finset.sum_eq_single` leaves exactly one actual summand in each component;
the genuine finite generator indices are 5 and 6. The result is `(0,-1)`.

`lower_eigenvalues_pos` uses the first contraction component, the sum of four
squares. If it were nonpositive, the three coordinate squares would vanish,
contradicting the nonzero eigenvector. Its strict positivity and the actual
first H-eigenpair equation rule out every nonpositive real eigenvalue. This
proves the required universal statement without computing any eigenvalues.

`lower_eigenpair_exists` proves continuity of the actual polynomial, its exact
endpoint values `F(0)=-1` and `F(1)=2`, and invokes Mathlib's actual
`intermediate_value_Ioo`. The resulting root lies strictly in `(0,1)`.
Substitution into the already-proved contraction identities gives all three
H-eigenpair equations; `(1,0,t)` is nonzero. No root approximation, existence
premise, interval isolation, or assumption on a selected eigenvalue is used.

`upper_negative_eigenpair` proves the explicit vector is nonzero and satisfies
all actual order-six signed-power equations. Its strict negativity is supplied
by the retained kernel LeanCert point certificate. `counterexample` then gives
the original admissible parameters, the original lower premise, and the
negated upper conclusion. `not_inheritanceConjecture` applies this instance to
the complete original universal target with exactly the same generating vector.

The optional lower-pair existence theorem is unconditional and separate from
the original implication. The proof does not add a strong-Hankel condition,
associated-matrix positivity, or eigenpair-existence premise to the conjecture.

## Actual verification evidence

The command `lake build Solution` passed, reporting **2918 jobs**.
`verification/proof-build.log` has SHA256
`5a98938c840d22976e9d49390c564201b0483796cf31a620d6526ed4d3984d5c`.
All eight core declarations and seven public wrappers pass their actual
`#assert_trust kernel` commands and corresponding axiom printing with exactly
`propext`, `Classical.choice`, and `Quot.sound`. No proof or Solution source
contains a hole, custom axiom, native proof, or import of Challenge.

The separate `python3 verification/fresh_check.py` run also passed. It compiles
Definitions, Proof, Solution, and the frozen Challenge into a new artifact
prefix, then runs both actual-declaration inspections. The old project build
path is excluded. All six commands exit zero; only Challenge emits its seven
intentional placeholder warnings. Those placeholders are never imported by
Proof or Solution. The command record `verification/fresh-checks.json` has
SHA256 `229ef77996a9970dbac530f864684c55eb2db6864032ebde23909f275f5589f3`.
The driver confirms all seven complete normalized source signatures agree
with Challenge and the Comparator export list.

The explicit certificate term calls
`LeanCert.Validity.verify_strict_upper_bound_dyadic_checked` on the constant
negative-one expression with a degenerate interval `[0,0]`. Its checker fact is
proved by kernel reduction. The original certificate is visibly retained in
`upper_negative_eigenpair_proved`, which is consumed by `counterexample_proved`
and hence by the final negation. It is not an unused tactic invocation or a
native-execution shortcut. The fresh certificate/consumer inspection is
`verification/fresh-certificate.log`, SHA256
`9c6fcb560999d130c5238b67f79477783b7e717620015a6394e575471c7ad113`.

The environment traversal in `verification/InspectProof.lean` visits 46
project declarations, including private helpers, and requires 14 actual
dependencies. These include the single-summand/product-zero theorems, genuine
ordered-pair reindexing, actual open-interval IVT, the checked LeanCert
certificate, and every substantive export implementation. The complete graph
and all seven elaborated signatures are in `verification/fresh-inspection.log`.

All ten dependency Git trees are clean and match the manifest pins. Lean is
4.33.1, Mathlib is `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert is
`621a43d7cf21f87872392a01e874f2f1dbddc926`. These macOS checks reuse the pinned
compiled dependency cache; they are not a claim of a full source rebuild or
Linux Comparator verification.

The proofs use exact finite sums, polynomial identities, and IVT. There are
no interval subdivisions, numerical tensor-eigenvalue searches, or large
computational certificates. The single rational point check directly supports
the strict negative eigenvalue used by the complete counterexample.

## Required next gates

Two independent final referees should review the actual source and the frozen
statement correspondence, independently re-elaborate the code, and verify the
retained dependency chain and axiom boundary. Root then handles truthful
schema-v0.4 metadata and Linux preparation. The real repository workflow must
still pass all kernel, Comparator, sandbox, and negative-control checks before
any formal-verification status promotion. No such result is claimed here.
