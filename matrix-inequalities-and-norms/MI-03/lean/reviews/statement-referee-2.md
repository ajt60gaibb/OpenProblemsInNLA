# MI-03 independent statement referee 2

**APPROVE the frozen eight-export statement boundary. No mathematical correction
is requested.** This is approval of the complete definitions, required numerical
and analytic conclusions, and source correspondence before implementation. It
proves none of the eight Challenge theorems, and does not certify Linux or final
formal-verification status. Both independent statement approvals must be present
before the implementer starts a proof.

Reviewer: OpenAI Codex agent `/root/leancert_examples`, 12 September 2026. I did
not author or edit these statements, the candidate witness or its proof plan.
I read the actual source and formal declarations, independently reconstructed
exact data, and freshly elaborated the statements. I did not consult the current
statement referee 1's report before reaching this verdict.

## Hash-bound inputs and source fidelity

The statement freeze `reviews/statement-freeze.json` has SHA256
`0243fca8b3e04b5dd3ee9d79f3fa9e25a4c706519089fbece2984178d11f7804`.
The handoff has SHA256
`6c16f5c268ddcac6f7d738bd6494007c17dd660955870afefc1572bba09a9b86`.
Every one of its **27 project files and eight original sources** matched before
and after this review. Each original also matched its actual Git blob at base
`c0601d8825e9f9e744212c62e6a43fefc1c60a22`.

| Boundary | SHA256 |
| --- | --- |
| Definitions | `12f5c9c25dc68e0032679b76cb9d328279ce803b4de437db8e1a564c499c7de6` |
| Challenge | `6d7905413c8234a816c79287e58eddcf0ff6267c043336392744c3e30b68fb34` |
| Exact numerical targets | `f0d052c0d6041ce9b22b804d3d13c1fc1d4a74b48b02b2b85ad2715c343654f0` |
| Source map | `719db4f1ee02a211fc12c649afac45c674b208eb45cf6887a456044ec016b1a2` |
| Comparator configuration | `640a5c0c1285346f6f09bec7260d4f204308ea711396c0688e9230574be46aa7` |
| Lake registration | `e561b053e35ceb41bba21b7d80726d63a07c889d85125fbb26a1b73b55e6093e` |
| Dependency manifest | `d81cba6c2f4f242306f1668f7f50feb1adb7b09964440a18e56429e0f96b2335` |

I read the complete canonical README and generated problem TeX, the complete
exported Colbrook solution TeX and submission note, the complete original
MI-03 proof, the retained informal review, Definitions, Challenge, numerical
specification, source map and package README. The source PDFs were checked for
byte identity; I do not claim new visual inspection of those retained PDFs.

I additionally checked the primary Bourin–Lee v3 text. Corollary 4.4 treats
general contractions and gives the universal k/4 upper bound; the conjecture
following Remark 4.5 asks odd-k optimality. This agrees with the complete
canonical question, without introducing a Hermitian restriction or a new
literature-status claim. [Primary text, Section 4](https://arxiv.org/html/2307.02034v3#S4).

## Complete original target and actual objects

`AdmissibleConstant k c` requires a nonnegative real c and quantifies over every
positive natural dimension n and every k-tuple of square **complex** matrices
with their actual induced Euclidean operator norms at most one. The original
inequality is represented by positive semidefiniteness of exactly
`cI + Σ|A_j| − |ΣA_j|`. There is no Hermitian, positivity, invertibility,
commutation, fixed-dimension, generic-position or rational-data premise. Zero
and singular contractions are included. The original n=1 cases are retained;
dimension two is used only for a lower-bound construction against the universal
constant.

`matrixModulus A` is `CFC.sqrt (A.conjTranspose * A)`, the **right Gram** positive
square root. I checked the actual elaborated matrix multiplication, conjugate
transpose, matrix order and CFC instances. The pinned CFC definition is the
nonunital calculus of NNReal.sqrt, with the actual positive square and uniqueness
theorems; it is well suited to singular inputs. The Gram positivity and square
identity required to use it are mathematical obligations of the exports, not
assumed certificates or a replacement definition of absolute value.

`operatorNorm A` is the norm of `Matrix.toEuclideanCLM A` on complex Euclidean
space. The actual witness-vector norm elaborates with `PiLp.instNorm` at exponent
2 on `Fin 2 → ℂ`, not with the sup norm of the underlying plain function space.
`shiftedSquare` elaborates as the ordinary **natural matrix square** from
`Matrix.semiring`; it is not entrywise squaring. `outerProduct u v` conjugates
the second vector and thus denotes uv*. All finite dimensions and tuple indices
have their expected actual Fin types.

`admissibleConstants` is exactly the set defined by that complete universal
predicate. `sharpConstant` is its actual real sInf, with no supplied sharp value.
The required `sharp_constant` export first asserts **IsLeast** of the actual set
at k/4. That includes membership and the lower bound against every admissible
c, establishing nonemptiness and attainment; its accompanying infimum equality
cannot rely on a totalized empty-set convention. The actual library
`IsLeast.csInf_eq` gives the expected bridge. `OddContractionConjecture` then
quantifies every odd k≥3, exactly the canonical target. Proving the stronger
supporting assertion for every k≥2 is legitimate and does not change the
original problem. The excluded k=1 need not satisfy the claimed k/4 value.

## Upper bound and exact positive decomposition

The first two exports require genuine modulus positivity, R²=A*A, equality of
its operator norm with A's norm, and the PSD consequences I−R and R−R² for every
contraction. These are true for the entire singular/zero-inclusive class: the
positive modulus spectrum lies in [0,1], where x−x² is nonnegative. The actual
C-star norm/order and CFC APIs inspected provide suitable existing machinery;
no external inequality is hidden in a premise.

I independently expanded the noncommuting finite identity. Half the ordered
sum of `(A_i−A_j)*(A_i−A_j)` is the unordered pair variance, because swapping
i,j gives the same Gram term and diagonal terms vanish. Distributivity gives
`k Σ A_j*A_j − (ΣA_j)*(ΣA_j)`. Combined with the true modulus square identities
and the Hermitian shifted square, the right side reduces to
`kT − kR + k²I/4`, precisely the scaled error gap. The real-to-complex casts and
k/2, k/4 coefficients match.

The unconditional PSD conclusions in `positive_decomposition` concern the pair
variance and shifted Hermitian square. It correctly does **not** assert
unconditional positivity of each `|A_j|−|A_j|²`; that term needs the original
contraction hypothesis, available in `universal_upper_bound`. Under that
hypothesis every term is PSD, and k≥2 permits division by the positive scalar
k. This proves the required full upper bound without any invalid general
matrix-order squaring or square-root monotonicity step.

## Every-k sharpness and independent reconstruction

The declared root is the actual complex exponential exp(2πi/k). The two required
facts, unit norm and the vanishing complete geometric sum, must be proved for
**every k≥2**. The pinned `Complex.isPrimitiveRoot_exp`,
`IsPrimitiveRoot.norm'_eq_one` and `IsPrimitiveRoot.geom_sum_eq_zero` have exactly
appropriate domains. No numerical phase list or finite range of k substitutes
for that requirement.

For all j the proposed vector is `(1/2, sqrt(3) ω^j/2)`, and the matrix is e1 vj*.
The identity `(sqrt 3)²=3`, with its actual nonnegative square root, gives unit
Euclidean vector norm. Its Gram matrix is the PSD projection vj vj*, whose
positive square root is itself. The required matrix norm-one and modulus
identities therefore have the correct direction and conjugation; they are
conclusions to prove, not fields assumed for a candidate. Summing all phases
and their conjugates yields the declared sum diag(k/2,0) and modulus sum
diag(k/4,3k/4). The first sum is already PSD, so its actual modulus equals it.
The declared difference diag(k/4,−3k/4) is correct.

For any admissible c, its original universal property applies at n=2 to these
actual norm-one contractions. Evaluating the resulting PSD error gap on e1
forces c−k/4≥0. Combined with membership from the all-dimension upper bound,
this gives actual IsLeast, actual sInf equality, and the complete odd-k result.
Neither finite diagnostic cases nor an assumed lower-bound certificate can
replace these universal proof obligations.

My independent [reconstruction script](statement-referee-2-evidence/reconstruct.py)
uses a four-coefficient rational quotient representation of Q(sqrt(3),i). It
imports no author reconstruction, root solver or floating arithmetic. It checks
algebraic roots of orders 2,3,4,6,12, all unit-vector/Gram/projection identities,
the actions A_j v_j=e1, every exact displayed sum and difference, and the
ordered/unordered/Gram variance identities. I also checked a separate k=5
cancelling tuple with noncommuting moduli and rational singular-value scales
1/2 and 2/3; this exercises the nonzero contraction-defect term in the positive
decomposition. All diagnostics passed. Their complete exact values are in
[reconstruction.json](statement-referee-2-evidence/reconstruction.json). They
check transcription and algebra; they are not a proof of the all-k exponential,
CFC, operator-norm or infimum statements.

## Independent elaboration, trust, standards and limitations

My separate-prefix Definitions, frozen Challenge and own actual-declaration
inspection all exited zero. The old project object directory was excluded from
LEAN_PATH. Only Challenge emitted warnings: exactly its eight intended holes.
All twenty definition-level `#assert_trust kernel` commands and actual axiom
reports use exactly `propext`, `Classical.choice` and `Quot.sound`. These audits
certify no Challenge theorem. My first inspection attempt used a nonexistent
pretty-printing option; I removed that option in my own inspector, retained the
initial log and source, and reran all three checks successfully. No candidate
statement or mathematical import changed to resolve that tooling issue.

This was local macOS arm64 with Lean 4.33.1. All ten dependency checkouts are
clean and match their locked revisions, including Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`. Matching compiled dependencies were
reused; this is not a full dependency rebuild or Linux Comparator run. The
configuration has all eight exact export names, no definition exceptions and
only the permitted standard three axioms. Its future Solution target is already
registered; current default Challenge remains appropriate to the statement stage.

I applied the relevant Tau Ceti correctness/faithfulness, scope, generality,
reuse and attribution rubrics through the repository's adaptation. The five
read rubric files match their archived immutable Git-tree blobs at
`afb424eda89e8ac96d9eb69f6a88972055a4cd1b`. Eleven relevant actual Mathlib source
files match the pinned Git blobs. The package advances one complete permanent
NLA target, and its bundled bridge obligations have concrete consumers. Existing
CFC, matrix, finite-sum, primitive-root and order APIs should be reused during
implementation rather than reconstructed as assumed structures. No speculative
roadmap machinery or official Tau Ceti endorsement is required or claimed.

I approve the stated **pure exact LeanCert kernel-trust-audit role**. There is no
numerical interval problem in this argument, so no decorative scalar interval
certificate is required or should be advertised. Final proof referees must still
inspect actual exported proof dependencies and all mathematical bridges. The
source's additional three-dimensional Hermitian extremizers and a separate rank
theorem are explicitly outside these eight exports and outside the canonical
odd-k question; that exclusion does not weaken the submitted target.

Colbrook's mathematical authorship, Bourin–Lee's conjecture/prior-bound credit,
and George Stepaniants's full Caltech department affiliation and AI-assisted
formalization attribution are preserved. I introduced no email or new priority
claim. Only my report and its evidence directory were written. No Proof or
Solution implementation, frozen statement edit, canonical promotion, ID change,
commit, push or publication occurred.

Reproduce my local checks with `python3
reviews/statement-referee-2-evidence/fresh_review.py`, the independent
`reconstruct.py`, and `audit_sources.py` in that directory. The retained logs,
actual expanded definitions/signatures, exact arithmetic, immutable source and
pin checks, primary-source observation and rubric evidence are bound by that
directory's `EVIDENCE-MANIFEST.json`. This approval is specific to the hashes
above; mathematical changes require re-review. Final proof, Linux and
publication gates remain pending.
