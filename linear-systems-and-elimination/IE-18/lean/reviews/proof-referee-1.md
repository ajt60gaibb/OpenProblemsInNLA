# IE-18 independent proof referee 1

Date: 2026-09-12. Reviewer: OpenAI Codex AI agent `/root`.
The reviewer did not author the IE-18 definitions or proof; the earlier role
was independent statement review. This is AI-agent review, not human peer review.

**Verdict: approve the complete negative formalization of the original target.**
No mathematical correction is requested. The actual Linux Comparator check
and publication evidence remain separate gates.

## Statement fidelity and proof

I read the complete canonical README and Colbrook manuscript at upstream
revision `5adea969c17391693978ada2674d25bb5c3daeb1`, the frozen definitions,
numerical targets and Challenge, and the complete Proof and Solution.
The following points were checked against the actual implementation.

- `FourStepConjecture` quantifies over every dimension at least two, every
  nonzero real symmetric matrix, and exclusion of one from the actual matrix
  spectrum. Positivity and diagonal form are properties proved about the
  counterexample, not restrictions added to the original universal claim.
- The actual map uses `A=I−M`, matrix-vector multiplication, the numerator
  `vᵀAv`, and denominator `∑ᵢ(Av)ᵢ²`, with an explicit zero branch. Its two
  compositions give the four original Anderson steps. The norm is explicitly
  `sqrt(∑ᵢvᵢ²)`; the different default norm on a function space is not used.
- The proof derives both nonzero vectors, the denominators `61/50` and
  `1381/93025`, the coefficients `90/61` and `3140/1381`, and both residuals
  from the actual map. Exact identities with positive rationals exclude a
  zero-division artifact. The actual squared amplification is then proved
  to be `1920682/21289638243`.
- The witness is proved positive definite using its three positive diagonal
  entries. Its complement is actually identified with
  `diag(9/10,1/2,2/5)` and proved positive definite. The spectrum is obtained
  from Mathlib's diagonal spectrum theorem; the exclusion of one is checked
  against those actual spectral values.
- The proposed factor uses Mathlib's full Hermitian eigenvalue list and all
  pairs of distinct indices. For its upper bound, actual eigenvalue membership
  in the proved diagonal spectrum reduces every pair to one of nine exact
  scalar cases. For the reverse bound, spectral range equality supplies actual
  indices for `1/10` and `3/5`; unequal values prove the indices distinct.
  Thus `1/121` is the true finite maximum, not merely a chosen pair value or
  a substitute list with an assumed ordering.
- The proposed factor `Λ=1/121` belongs to the **unsquared** norm ratio.
  LeanCert proves `1/14641 < 1920682/21289638243` in explicit kernel mode.
  The square-root identity and the order equivalence for squares of
  nonnegative numbers then give the required unsquared strict inequality.
  The additional square `Λ²` is retained at the correct step; no numerical
  approximation to a square root occurs.
- `IsGreatest` expresses actual membership and the upper-bound property of
  the entire amplification set. The proved nonzero witness puts its actual
  ratio in that set. Its strict excess contradicts the upper-bound property,
  after which the full universal statement is instantiated and negated.

The stronger parameter family and separate asymptotic convergence question
in the source are outside the advertised formal scope. A strict admissible
counterexample fully answers the original universal identity negatively.
No vacuous maximum, assumed spectral certificate, narrowed matrix class,
unproved analytic bridge, or omitted zero convention was found.

## Independent checks and applicable referee standards

I independently re-elaborated `NLA/IE18/Proof.lean` and `Solution.lean` with
`lake env lean` under Lean 4.33.1; both exited zero. The actual source was
re-elaborated, rather than accepting a cached build status. The five audited
internal declarations and all three public exports report exactly
`propext`, `Classical.choice`, and `Quot.sound`; their eight explicit
`#assert_trust kernel` checks pass. The [command record and raw outputs](../verification/referee-1/)
bind these observations. They do not claim authoritative Linux verification.

The Challenge placeholders are never imported by the solution dependency
chain. The public signatures agree with the frozen Challenge on inspection;
the independent mechanical Comparator check remains required. No custom
axiom, sorry, native-evaluation trust, unsafe proof shortcut, or hidden
mathematical premise appears in the proof.

The relevant Tau Ceti correctness, faithfulness, quality, generality, reuse,
API, naming, placement, documentation and attribution angles were applied
within this single-problem project. The implementation reuses standard
matrix, spectrum, finite-supremum and square-root lemmas. It splits the
noncomputable eigenvalue maximum into upper-bound and attainment arguments,
avoiding expensive eigenbasis computation. Exact rational vector algebra,
nine scalar pair cases and one LeanCert point certificate replace numerical
eigenvalue enclosures, sphere optimization and interval subdivision.

Matthew J. Colbrook retains credit for the mathematical counterexample;
George Stepaniants receives formalization credit with his approved Caltech
department and university affiliation. No contact email, human peer review
or official Tau Ceti service verdict is claimed.

## Frozen reviewed bytes

| File | SHA256 |
|---|---|
| `NLA/IE18/Definitions.lean` | `dc32a03d0ab95a1b3f41f864f90d30d56c3dd041330015caa059e253ff47b28d` |
| `Challenge.lean` | `97ad7cf8e2c3077d4cc52f587c9702627f06c8d915005804f044fd60c66ffd59` |
| `NUMERICAL_TARGETS.md` | `318f34ec1f88f111a83c1a6c869735ac2cc5640b5bdb34f89201e97607e9e890` |
| `NLA/IE18/Proof.lean` | `0244e39c88101ab7a998bb0c5da56549d668d46ae068e4fc2ef5067fabdf4f73` |
| `Solution.lean` | `d257fd0b3def07c4503f2e084407116661cac5e556d7fe46573c9f7f78c7c0c3` |
| `verification/referee-1/check-1.log` | `a1c311aeacf54f4cb8597ef5ccc15fa580c9ad7b2b3fb0e5ec9647e189319512` |
| `verification/referee-1/check-2.log` | `6fd13596bb2ac7acbe680bcec9fe045d65c16aa1b2d1558e6d531d64543a59f6` |

Substantive changes reopen the affected review gates. Final metadata must
retain this exact scope and distinguish successful local checks from the
pending fresh Linux Comparator result.
