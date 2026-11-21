# Assessment and computational reproduction - 19 November 2026

This is a target-and-consistency assessment with reruns of the author's
finite diagnostics. It is not a documented independent full-result proof
audit, external human peer review or formal verification. The proposed
status is **Solution claimed**.

## Mathematical correspondence and construction

The assessment compared Theorem 1.3 (manuscript p. 2) with both original
MF-11 questions and followed its construction and estimates in Sections 2-5
(pp. 4-13). The following obligations match the target:

1. The input is one finite pair of real 20-by-20 matrices, so it is a compact
   nonempty real family. The quantity g is the maximum over every switching
   word, in the Euclidean operator norm; it is not a single-word norm.
2. The claimed bounds n <= g(n) <= 6n^3 give joint spectral radius one by
   taking nth roots. Thus irregularity is asserted in the marginal regime.
3. The seven-dimensional algebra has YZ = 0 and Y^2 = -XZ^2. The word
   reduction in Proposition 3.2 represents arbitrary products, with norm
   comparisons in Corollary 3.4. For equal gaps of length m, the critical
   coefficient contains n/8^(2m) - 1/2^(2m), which vanishes at n = 16^m.
4. Proposition 4.4 bounds every word using effective multiplicities.
   Lemma 5.2 controls other gap lengths at the resonant time, and
   Proposition 5.3 compares that upper bound with explicit lower-bound
   words at half and multiplied times. The lacunary angle in Lemma 5.5
   and Section 5.1 produces an unbounded sequence of ratio bounds.
5. Taking k = N_j/2 and the positive increment N_j/2 contradicts the first
   original quantifier. Taking the fixed multiplier l = 2 contradicts the
   second. No assertion about invertibility or the low-dimensional
   extensions is necessary for this implication.

The issue's PDF and the archived Zenodo PDF are byte-identical. The three
scripts matched the MD5 identities in the Zenodo metadata. The retained
[SHA-256 manifest](../SHA256SUMS) identifies all inputs. This correspondence
and consistency assessment does not assert a complete new referee audit
of every analytic estimate or of Theorems 1.3-1.7.

## Fresh execution results

All three unmodified scripts exited with status 0, using their default
parameters and assertions enabled:

| Command | Supplied check count | Full output |
| --- | ---: | --- |
| `python -I -u verify.py` | 542,988 | [Main construction](verify.log) |
| `python -I -u invertible_blocks.py` | 119,958 | [Invertible construction and illustrations](invertible_blocks.log) |
| `python -I -u almost_linear.py` | 15,591 | [Almost-linear construction](almost_linear.log) |

The runs used Python 3.13.14 on macOS 26.7.2, arm64, with NumPy 2.3.5,
mpmath 1.3.0 and SymPy 1.14.0. [Machine-readable environment](environment.json).

The counts are the scripts' own finite-check counts. Their rational matrix
identities are exact. The exhaustive finite-word computations, random tests
and large-parameter diagnostics also use floating-point or multiprecision
arithmetic, as labeled in the outputs. The main and almost-linear scripts
use default maximum word length 16; the invertible script enumerates selected
tests through length 12 and includes additional illustrative finite families.
These runs do not establish the infinite-parameter theorem by enumeration,
prove the low-dimensional classification, or validate a Lean proof.

## Lean boundary

The attached source was read for its definitions and final declarations;
it was not compiled. It contains an explicit spectral-norm conclusion and
a compact-family negation with names listed in the [submission record](../README.md).
Its weaker displayed constants in `dips_spectral` still purport to imply
the same qualitative negative answer; the attachment is not represented
as reproducing every numerical constant or extension of the manuscript.

No toolchain/dependency pins, successful build log, transitive axiom output
or isolated statement-correspondence/kernel receipt were supplied in the
one-file ZIP. A source-level `#print axioms` command is not an executed axiom
report. The repository's requirements for **Lean verified** remain unmet.
