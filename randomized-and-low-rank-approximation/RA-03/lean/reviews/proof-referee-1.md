# RA-03 independent proof referee 1

Date: 2026-09-12. Reviewer: OpenAI Codex AI agent `/root`, who did not author
the RA-03 definitions or proof. The earlier role was independent statement
review. **Verdict: approve the complete negative formalization of the original
target.** This is AI-agent review, not human peer review. Fresh Linux
Comparator verification and publication evidence remain required.

## Actual target and mathematical proof

I read the complete canonical target and the entire shared Colbrook manuscript
for the statement review, and now read every line of the frozen Definitions,
Challenge, completed Proof and Solution. The proof retains the originally
approved boundary. The canonical randomized LU claim is not replaced by
Cholesky, a different pivot distribution or a norm other than squared
Frobenius error.

The universal assertion includes every complex rectangular matrix, positive
row and column dimensions, and every `1≤k≤min(m,n)`. The conditional pivot
mass is the squared modulus of the joint entry divided by the current
squared Frobenius norm. It does not factor row and column choices or treat
successive pivots as independent. The actual cross update uses that selected
entry and current residual. At zero, an absorbing label has mass one; a zero
entry otherwise has mass zero, so its totalized identity update cannot change
the expectation.

The norm bridge uses the explicitly scoped Frobenius matrix norm. Expanding
that norm and applying the square-root square identity yields the exact sum
of squared complex moduli. Nonnegativity and its zero characterization follow
from genuine norm lemmas. This excludes a hidden default operator or entrywise
maximum norm and proves the denominator is nonzero whenever the residual is
nonzero.

`pivotMass_sum` treats zero and nonzero residuals separately. In the latter
case, summing all joint entry labels gives the actual Frobenius numerator
divided by itself; the nonzero-denominator premise is proved. Nonnegativity
is established for every label. `historyMass_sum` uses the proved `Fin.consEquiv`
to split a complete history into its first pivot and remaining conditional
history, then inducts for arbitrary dimension, residual and length. It proves
normalization of the actual joint law, not a selected finite witness table.
Zero-dimensional supporting cases are valid as well: the unique zero matrix
is absorbed, and the optional-label type remains inhabited.

The expectation is defined as the finite sum over **all** complete histories
of joint mass times terminal squared error. The proof derives both its
zero-step value and the usual one-step conditional-expectation recurrence
from the actual history definitions and the same finite equivalence. The
concrete expectation then sums every jointly sampled entry, with the absorbing
label explicitly shown to have zero mass at the nonzero witness.

For `A=[[2,1],[1,2]]`, the proof establishes every nonzero entry, squared norm
ten, and actual Gram identity `AᴴA=[[5,4],[4,5]]`. It derives the four masses
`2/5,1/10,1/10,2/5` from the algorithm and the four errors `9/4,9,9,9/4` from
the actual nonzero branch of the cross update. Thus the true expected error
is exactly `18/5`. The numerical table is a proved output, not an assumed
probability or residual certificate.

The singular-value bridge is also actual: the Euclidean matrix linear map's
adjoint composition is proved equal to the linear map of the Gram matrix.
The characteristic polynomial is exactly `(X−9)(X−1)`. The inspected Mathlib
`sort_roots_charpoly_eq_eigenvalues` identifies the descending real parts of
the full characteristic-root multiset with the actual symmetric operator
eigenvalues, including multiplicity. Evaluating that two-element sort proves
the ordered list `[9,1]`. The inspected `singularValues` definition and
`singularValues_of_lt` then give the actual square roots `3,1`; no proposed
spectral list, characteristic polynomial, ordering or singular value is
assumed. The zero-based tail `[1,min(2,2))` consequently equals one.

One explicit kernel-mode LeanCert certificate proves `2<18/5`. Rewriting by
the proved actual expectation and tail yields the strict reverse inequality.
The final theorem instantiates every original dimension/rank hypothesis at
`m=n=2,k=1` and contradicts the full universal bound directly. This settles
the canonical yes/no question negatively. The shared source's stronger
all-rank sharp `4^r` result and Cholesky conclusions are not formalized or
claimed by these exports.

## Independent checks, trust and proof quality

I independently re-elaborated Definitions and Proof into a separate local
output directory and then re-elaborated Solution with those fresh artifacts
first in its import path. All three commands exited zero. The eight audited
internal results and four public exports report exactly `propext`,
`Classical.choice`, and `Quot.sound`, with all twelve `#assert_trust kernel`
checks passing. [The command record and logs](../verification/referee-1/)
record the actual macOS run, timing and hashes. The initial review-only import
attempt lacked Definitions in that separate directory; its failed log is
retained. Compiling both modules there fixed the review environment without
changing any mathematical source.

No custom axiom, native-evaluation trust, sorry, unsafe proof shortcut, hidden
assumption or import of Challenge was found. The four deliberate Challenge
placeholders remain isolated from the Solution chain. The actual public
signatures match the frozen Challenge on inspection. Linux Comparator must
still check their mechanical identity, transitive trust and kernel acceptance.

Relevant Tau Ceti correctness, fidelity, scope, quality, generality, reuse,
API, naming, placement, documentation and attribution angles were applied
within this project. The proof reuses norm, finite-equivalence, characteristic
polynomial and singular-value APIs. It proves the generic probability law
analytically instead of enumerating arbitrary histories, and computes only
four concrete updates and a two-root spectrum. There is no interval
subdivision, approximate square root or numerical eigenvalue search. Helper
names expose the actual probabilistic and spectral bridges; the export
wrappers deliberately reproduce the reviewed target signatures.

George Stepaniants receives formalization credit with the approved Department
of Computing and Mathematical Sciences, California Institute of Technology
affiliation. Matthew J. Colbrook retains mathematical authorship. AI assistance
and independent agent review are disclosed without publishing George's email
or claiming external human endorsement.

## Bound source bytes

| Input | SHA256 |
|---|---|
| `NLA/RA03/Definitions.lean` | `de6509ef6b4a41db3e01fce7b77af4c7c338dbd61f8f135e956602d3b8b0980f` |
| `Challenge.lean` | `74a7c727e8cf2fa1ee26e78cfab812626b265abe8211e09f144a3c78fca5345e` |
| `NUMERICAL_TARGETS.md` | `91618c7848ad46931a8f59bad6ff2900bf53b1e1dde22f31383c4a3941eb4a94` |
| `NLA/RA03/Proof.lean` | `b98c702906e163805ae83809cf750eca650f365a815034a665e2ebd7bd96746a` |
| `Solution.lean` | `08e83996051e2c443a6a5153e8fb6e30ebf69bd4f44f86cddda837bbc0baf86e` |
| `verification/referee-1/proof.log` | `3fb305e7ece5112c4e3a964440393ad7326fce3e2d5261af23580a85bbe607e3` |
| `verification/referee-1/solution.log` | `d730e3f1aacb07083c7b89c63a0afc75b3c3881cd88c0b212bed18aad8568d52` |

Substantive source changes reopen the affected gates. Final metadata and
catalog wording must preserve this complete negative target and separately
state the status of the still-required authoritative Linux check.
