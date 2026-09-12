# OpenProblemsInNLA — partial proof and verification bundle

## Status at a glance

**This is not a completed three-hour session and not a solution to the category.**
The earlier attempt produced no proof bundle. The work here was carried out
actively during the subsequent reply to “so?”. No research is claimed during
the reminder interval or after delivery.

**Full remaining repository targets resolved: 0 of 13.**

The bundle contains four proof manuscripts. Their limited statements have
complete written arguments; the finite SP-08 conclusions additionally depend
on the included exact-integer computer certificates. They have not received
independent external review or formal verification. No originality, priority,
human authorship, institutional affiliation, or publication claim is made.

The source snapshot is repository commit
`f41f1f9ffa2171550d4bb795862c6170c4f26070`. It lists seven OPEN targets and six
PARTIAL targets in this category. Source identifiers and the requested order
are recorded in `sources/snapshot.json` and `notes/TARGET_STATUS.md`.

## Main deliverable: exact finite SP-08 results

For real symmetric matrices whose entries are in the indicated interval,
including unrestricted diagonal entries within that same interval, the bundle
proves:

| Dimension and interval | Maximum spectral spread | Rank-two attaining block size |
|---|---|---:|
| 8, `[1/2,1]` | `sqrt(73)` | 2 |
| 10, `[0,1]` | `sqrt(133)` | 3 |
| 11, `[0,1]` | `sqrt(161)` | 4 |

The proof first reduces every dimension and interval to at most `2^(2n-1)`
signed-threshold patterns. It then checks all such patterns in the three
specified cases, not a random sample. The runs cover 32,768, 524,288, and
2,097,152 patterns, respectively. Integer characteristic-polynomial computation,
explicit overflow bounds, and arbitrary-precision polynomial-shift certificates
supply the upper bounds. Explicit rank-two matrices attain them.

These cases are beyond the particular finite ranges recorded in the pinned
SP-08 README. That does not establish novelty in the broader literature.
The all-dimensions, all-intervals conjecture is still not proved.

## Manuscripts

- `proofs/SP-08_signed-threshold-reduction-and-finite-cases.md`: the general
  finite-family reduction and the three complete computer-assisted finite cases.
- `proofs/SP-09_two-point-spectrum-amplification.md`: an exact formula for
  unitary-orbit distance when one normal matrix has at most two distinct
  eigenvalues, proving finite-amplification invariance for that subclass and a
  corresponding constant-one SP-07 subclass bound. General SP-09 and SP-07 are
  not settled.
- `proofs/SP-03_skew-multiplier-reduction.md`: a saturated quartic multiplier
  system for generic symplectic critical points, with a proof that singular
  denominators do not occur at generic actual critical points. The known
  `D_1=4` is rederived as a check; the general degree formula is not evaluated.
- `proofs/KE-02_weak-coupling-diagonal-separation.md`: an `O(n log n)` diagonal
  construction under an explicit weak-coupling condition, plus an unrestricted
  order-two construction. It does not meet the full target for arbitrary
  normalized tridiagonal matrices.

## Verification materials

`certificates/` contains all three final exact certificate sets.
`verification/` contains the verifier/generator, exact algebra checks, clearly
labeled numerical smoke tests, and execution logs. The final certificate sets
have no failed or unchecked polynomials. Full coverage was regenerated for all
three cases. The order-eleven certificate and coverage checks were also run in
separate calls to respect execution-call limits; both passed.

No log labeled PASS represents an independent Codex review or a Lean proof.
The PASS labels refer only to the tests described in those logs.

```bash
python verification/spread_exact.py verify certificates/SP-08_n8_a-half.json
python verification/spread_exact.py verify certificates/SP-08_n10_a0.json
python verification/spread_exact.py verify certificates/SP-08_n11_a0.json
python verification/algebra_checks.py
```

The three certificate verifications require Python and NumPy. The supplemental
algebra checks also require SymPy. Tested versions were Python 3.13.5, NumPy
2.3.5, and SymPy 1.14.0. There are no network calls in the verification scripts.
See `verification/README.md` for generation commands and audit details.

## Codex handoff

Start with `HANDOFF_TO_CODEX.md`. In particular, independently audit Theorem 1
of the SP-08 manuscript before relying on the exhaustive certificates: it is
what connects the finite enumeration to the continuous matrix optimization.
Check novelty and the latest repository state before proposing additions.

**Do not mark any of the 13 original targets SOLVED on the basis of this bundle.**
No branch, commit, issue, or pull request was created and no GitHub content was
modified. This archive is a review handoff, not a repository patch.

`SHA256SUMS.txt` records the contents of the delivered bundle other than itself.
