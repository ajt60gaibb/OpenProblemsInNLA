# RA-08 independent final mathematical referee 1

**Verdict: APPROVE the complete frozen mathematical implementation.** No
mathematical correction is requested. This is an independent AI-agent review,
not external human peer review, official Tau Ceti certification, or approval
of a Linux run or publication. Canonical status remains **Solved**.

Reviewer: `/root/leancert_examples` (OpenAI Codex). I authored neither the
RA-08 statement boundary nor its implementation. I previously read some
RA-08 definitions while preparing the separate RA-09 statement package; that
did not contribute to RA-08. The author checks and other referee's opinion
are not substitutes for the independent work recorded here. Review completed
2026-09-12 America/New_York (fresh checks ran 2026-09-13 UTC).

## Exact reviewed boundary

The project is `randomized-and-low-rank-approximation/RA-08/lean` at base
`5830ed4fb06da0659414a3deb2a40ad327aca052`. I verified every file in the
450-file implementation freeze, all 39 original statement inputs, and all
10 original source files against both their SHA-256 identities and immutable
Git blobs. These inputs remained unchanged before and after my checks.

| Input | SHA-256 |
| --- | --- |
| `verification/proof-freeze.json` | `ab05e2bf801e6906453e88a4d84d5e73191f776db05610fb8b8e5e4a03d4f856` |
| `reviews/proof-completion.md` | `dab07a0cf99d739914c54efea282211afcbfb45507ac3fef74b285afc3ad79ce` |
| `reviews/statement-freeze.json` | `eb0460c3dd4c13a42f928e3f00c9c3710e486922b99aff74f4d6a3098c5ed332` |
| `NLA/RA08/Definitions.lean` | `8c2f3a76e44730b1f9d5bc8e896070c10868bae817d0c3d11ace22b3c7d94c41` |
| `Challenge.lean` | `6dfe1fe49431bd3f5dc4c91360911d02c6aaf73d902a40fcabec79155fb11c18` |
| `NLA/RA08/Proof.lean` | `8e225fd88e4fb1d546a26241f835dca9ee08756cc52e3f7fe640ba8b11cf8318` |
| `Solution.lean` | `7dc0f17661a7eead3e4555bbc692ebcc0add5e10b8c6414d51f2cd43c69730cc` |

I read the full canonical problem, Colbrook's complete manuscript
`03_concave_transfer_counterexamples.tex`, its informal review, both statement
approvals, the numerical plan, source correspondence, proof map, all sixteen
mathematical source modules, and all fourteen Solution exports. The manuscript
is *Concave matrix-function error transfer can fail for exact Nyström
approximations*, SHA-256
`6f52104ffcbc29ab7fa2de47537bfe2be7a2a3f56bf2e2c65d090036680cb0ed`.

## Mathematical findings

The last export negates the complete canonical claim. It retains every real
PSD matrix pair with the actual PSD order, every original dimension, rank and
error parameter, the entire admissible half-line function class, and every
ordered orthogonal eigendecomposition. In particular, generic admissibility
does **not** assume `f 0 = 0`. The truncations use the selected eigenbasis and
discard coefficients to zero, including when `f 0 > 0`.

The operator norm is the actual real Euclidean continuous-linear-map norm of
`Matrix.toEuclideanCLM`. The function application is actual real `cfc`.
The generic obligations are proved: ordered eigendata exist; their finite
spectral calculus is the genuine CFC; the first discarded eigenvalue gives
the operator norm of the tail; and the absolute quadratic form is bounded by
the true operator norm times the squared Euclidean norm. No claimed numerical
spectrum, preferred eigenbasis, diagonalizability assumption, or oracle norm
appears as an extra premise of the final counterexample.

I checked the substantive proof chain directly:

* The sorted spectral-theorem construction and arbitrary-basis reconstruction
  prove nonvacuity. The finite-spectrum CFC map is identified by the actual
  continuous star-algebra-map uniqueness theorem, including its map-of-the-
  identity obligation. This also justifies arbitrary real extensions outside
  the nonnegative spectrum.
* The unchanged six-dimensional source witness has `k = 3`, `t = 1/65536`,
  `a = 17/16`, `b = 127/128`, `Ahat = diag(1/2,b,a,0,0,0)`, and
  `A = Ahat + t F`. Exact symmetry, Gram/projection identities, PSD order and
  positive definiteness are established for the actual matrices.
* Actual eigenvectors and a positive compression exclude the interval `(1,a)`
  from the spectrum. The two rectangular-kernel dimension arguments, together
  with the stated quadratic restrictions, give the fourth eigenvalue exactly
  `t` for **every** ordered basis of `A`, and zero for `Ahat`. No decimal
  eigenvalue enclosure substitutes for these arguments.
* The function is the admissible `min x 1`. The degree-six polynomial minorant
  agrees on the required `Ahat` spectrum and lies below this function on the
  proved spectrum of `A`. The proof of this scalar inequality includes the
  full unbounded shifted polynomial, not merely sampled values.
* `cfc_mono` is applied to two scalar functions on the same matrix's actual
  spectrum. It does not assume that the kink function is operator monotone
  for different matrices. The exact CFC polynomial identity and symmetry
  reduce the squared polynomial quadratic form to three matrix-vector
  products and a sum of six squares.
* Both optimal spectral tails are exactly `t`, the original residual is `t`,
  and the transformed residual is strictly larger. The material strict gap,
  Rayleigh bound, and eigendata existence yield the complete universal
  negation at `epsilon = 0`.

The exports do not claim the manuscript's larger contour-method ratio,
separate Nyström identity, ancillary nuclear-norm result, all-constant
extension, or historical priority. None of those additional results is
needed to refute the canonical implication.

## Independent exact reconstruction

My restricted-AST/Fraction script parses the frozen rational literals and
independently reconstructs the source block matrix, both projection Gram
identities, exact positive LDL pivots for `A` and the relevant compression,
the fixed residual eigenvector, all three matrix-vector products, the full
polynomial-square diagnostic, and every shifted scalar coefficient. It does
not call the author's numerical checker or use approximate eigenvalues.

For `w = (4,3,1,0,0,0)`, it independently gives `||w||^2 = 26` and
`w^T F w = 14912/585`. With the actual polynomial minorant, the relative
excess over `26 t` is exactly

```
78605142319958855341529309 / 11432529876841442781954048000 > 0.
```

The coefficients of `1 - h(a+z)` are zero followed by the six positive
rationals recorded in the reconstruction. These finite diagnostics detect
transcription mistakes; the general spectral, scalar and full-negation
arguments are supplied by the inspected Lean proofs.

## Fresh proof, trust and dependency checks

I independently ran twenty direct Lean commands in a new project prefix:
all sixteen mathematical modules, Solution, the actual author inspector, my
own type-and-body inspector, and the isolated Challenge. All returned zero.
There were no implementation or inspector warnings; Challenge emitted
exactly its fourteen deliberately isolated reference-hole warnings.

Lean was `4.33.1`, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. All ten dependency repositories
were checked clean at the manifest commits before and after reuse. Only the
matching MI-22 dependency artifacts were read; old RA-08 and MI-22 project
objects were excluded. No Lake build, dependency copy, download or dependency
rebuild was performed. Fresh generated objects were hashed and then removed
from my own disposable prefix; the source snapshots and raw logs remain.

All fourteen Solution signatures exactly match Challenge, and the comparator
selects those fourteen exports, no substituted definitions, and exactly the
three permitted axioms. The fresh checks produced **61 standard-three axiom
records**, each accompanied by the relevant kernel trust checks. My traversal
of actual theorem types **and** proof bodies from the full negation reached
**215 safe project declarations** and retained all **33 specified material
dependencies**. It rejects project axioms and unsafe declarations. No
implementation `sorry`, `admit`, native trust, review-module import or
Challenge import was found.

I inspected the actual retained helper
`NLA.RA08.numerical_gap_positive_proved._proof_1_7`. Its type is the strict
upper-bound Boolean checker for the constant zero on `[0,0]` with the exact
positive rational displayed above as the strict upper bound, precision `-53`
and depth `10`. Its proof is kernel reduction
`of_decide_eq_true (id (Eq.refl true))`. The enclosing proof consumes
`LeanCert.Validity.verify_strict_upper_bound_dyadic_checked`; that dependency
is retained through the actual counterexample and full negation. This is a
material explicit-kernel point certificate, with no interval subdivision.

The local check is macOS. It does **not** establish the later authoritative
Ubuntu default-kernel replay, official Comparator result, or negative-control
behavior. Those operational gates remain pending.

One **reviewer-only Python display assertion** initially failed after all
twenty Lean checks had passed: the deep `pp.all` output elided the displayed
matrix-map value, and the CFC print includes explicit universe arguments.
The original audit script and initial diagnostic are retained. The corrected
audit checks the printed genuine Euclidean norm instance, exact frozen
definition, retained actual norm bridges, and normalizes only printed
universe syntax. Its correction record also corrects the initial brief
diagnostic's identification of which conjunct was absent. No candidate or
Lean proof change was made.

## Review standards, evidence and packaging follow-up

I applied the repository's `docs/lean/REVIEW.md` adaptation of the twelve
Tau Ceti rubrics at commit `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`, checking
correctness, complete statement fidelity, actual definitions and assumptions,
dependency trust, architecture, naming, simplification and avoidable
computation. The exact spectral/compression and polynomial route avoids
computing sorted numerical eigenvalues or a six-dimensional interval
subdivision. The actual pinned Mathlib CFC/operator-norm APIs and LeanCert
soundness chain were read; their file hashes and commits are in the audit.
There is no blocking design or mathematical finding under the repository's
adapted standards.

The frozen README and manifest still describe the historical statement phase.
They correctly stayed untouched during this review. Before candidate
publication they must be archived and refreshed to describe the completed
proof/reviews truthfully; the manifest should use the full actual manuscript
title above. The numerical plan and source correspondence remain historical
statement-boundary evidence. This is a packaging follow-up, not a requested
mathematical change. Preserve Colbrook's mathematical attribution and George
Stepaniants's formalization credit with Department of Computing and
Mathematical Sciences, California Institute of Technology, Pasadena,
California, USA; no George contact email is required or approved here.

The independent evidence is in `final-referee-1-evidence/`:

| Evidence | SHA-256 |
| --- | --- |
| `audit-result.json` | `dccf08d2463c5a26a051bcf677bbdf6bc6508735d275172e748141e7bd139389` |
| `attempt-0zbwr1pg/result.json` | `83681a676aad549a13b744f6a1459a1ccff7f5c1d8950b128548c0b8464093dd` |
| `attempt-0zbwr1pg/reviews-final-referee-1-evidence-Inspect.log` | `0e4ffc14bed596f307a6c8c3c5076566c7a93ba70c1fa0e20d3a22089f237e40` |
| `exact-reconstruction.json` | `eff4f4bf02594cba67c880b48da185e70baea8cca3f512677ced37a56503ff94` |

Its `EVIDENCE-MANIFEST.json` binds this report and every independent evidence
file, including nested correction records. Only that exact outer manifest
is excluded from its own inventory. I made no frozen source, canonical,
registry, commit or publication change.
