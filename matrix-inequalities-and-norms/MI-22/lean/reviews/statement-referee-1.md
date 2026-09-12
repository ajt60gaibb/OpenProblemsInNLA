# MI-22 independent statement referee 1

**APPROVE the frozen eight-export statement boundary. No mathematical statement
correction is requested.** This approves definitions, exact numerical targets
and required conclusions before implementation. It does not prove any of the
eight Challenge theorems or certify a Linux verification run. The second
independent statement approval remains necessary before implementation begins.

Reviewer: OpenAI Codex agent `/root/solved_statement_inventory`, 12 September
2026, independent of author `/root/leancert_examples`. I did not write or edit
the mathematical statements or the adapted witness. I reached this verdict by
reading the source mathematics and actual definitions, independently
reconstructing the finite data, and freshly elaborating the statement modules.
I did not read statement referee 2's conclusions before reaching this verdict.

## Exact reviewed inputs

The [statement freeze](statement-freeze.json) has SHA-256
`d83d2a2baa1788f6e5ec284c70bb12d7618f4963a9426777a37b2af4135ed756`.
All **27 frozen project files and eight original sources** match their recorded
hashes before and after review. Each original source also matches its Git blob
at `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`.

| Boundary | SHA-256 |
| --- | --- |
| Definitions | `3a9398c2da3be1c71fd59de483042153cae1af55226f4b61ca9d7bd977ffd8f8` |
| Challenge | `503cc7280458d3a1dcc4c3a03b91bcb3ae7e7940961dcd12d86736a133923179` |
| Numerical targets | `3798f0d25414815e683cabfc77ab776a2a22e4929c1fab0ea4f49fbde8187c66` |
| Source correspondence | `e501e9b1476986cf0764067bd5672b0dbdb4261a9daf99ddcb5c7f13b548c95b` |
| Comparator configuration | `c388b280ae7f5b5ce037bda2ccfec4c833b48c954c2d77d09d3143beaff2d961` |
| Lake manifest | `71e8401646a361d36b841337a9e08cbe0633fbbbce8e5ce9b5db0e10dfefbb5c` |
| Statement handoff | `fc0be477ed453bec390a7002e13e2002f740e0b0d257550bcc9e8cc85385b1cb` |

I read the full canonical README and statement in its TeX, complete exported
`solution.tex`, complete original Colbrook proof, submission note, retained
informal review, complete numerical specification and correspondence, and every
Definition and Challenge declaration. Source PDFs were checked for byte identity;
this does not claim a new visual inspection of those retained PDFs.

I also read the actual primary preprint through PDF text extraction. Its printed
pages 1–3 specify complex matrices, descending singular values from the positive
modulus, the distinction between full and weak log-majorization, the weighted
mean and Conjecture 1.1. These agree with the canonical positive-definite target;
the paper's broader semidefinite domain contains the proposed strictly
positive-definite counterexample. No new regularization theorem or literature
status survey is asserted. [Ghabries–Abbas–Mourad–Assi, primary preprint](https://arxiv.org/pdf/2105.13356).

## Full target and actual semantics

`WeightedLogMajorizationConjecture` retains every positive integer dimension,
every complex positive-definite pair `A,B`, and every real `t` in the closed
interval `[0,1]`. The left product has the exact original noncommuting order
`A^t (A#_tB) B^(1−t)`, and the comparison matrix is the actual product `AB`.
There is no real-only, fixed-dimension, rational-exponent, commutativity, rank,
root-existence or numerical-certificate assumption in the universal statement.
Its final export is its unconditional negation.

`SingularLogMajorized` retains every proper nonempty prefix product and equality
of the full products at dimension `n`. The zero-based range is exactly the
original one-based first `k` values. The case `n=1` still includes its full-product
equality; it is not silently omitted. A failure of `k=1<n=3` can disprove this
conjunction without replacing its definition by a first-value-only predicate.

The singular values are the actual Mathlib values of `Matrix.toEuclideanLin A`
on **complex Euclidean space**. The pinned library constructs them from the
square roots of the full ordered eigenvalue family of the true adjoint
composition and extends the sequence by zero beyond the dimension. The spectral
family comes from an orthonormal eigenbasis, retaining multiplicities; this is
not a user-supplied eigenvalue or singular-value table. The generic
`singular_values_semantics` conclusion requires nonnegativity, descending order,
zero extension, the exact adjoint-composition formula and equality of index zero
with the actual induced operator norm. Its dimension proof identifies the true
complex dimension with `n`.

`spectralPower` is actual `CFC.rpow` in the standard ordered complex matrix
algebra. The generic `spectral_power_semantics` statement requires its actual
principal spectral representation for every PD matrix and every real exponent.
The normalized factor in the weighted mean keeps both inverse half powers in
their original positions. The definition does not replace any matrix power by
the proposed rational witness values.

`operatorNorm A` explicitly means the norm of `Matrix.toEuclideanCLM A`.
`witnessVector` is genuinely in `EuclideanSpace ℂ (Fin 3)`, and `witnessTestValue`
is the real part of an actual coordinate after applying that continuous linear
map. `frobeniusSquared` includes all squared complex moduli. The generic action
and Frobenius bounds are explicit required conclusions, not assumptions or
entrywise-norm substitutes. I inspected the elaborated instances for these
objects, ordinary matrix multiplication and natural matrix powers.

## Adapted witness, attribution and exact reconstruction

The change of witness is disclosed consistently in Definitions, numerical
targets, source correspondence and handoff. `A=diag(256,1/256,1)` is unchanged
from Colbrook. The candidate uses

```
D = diag(16,1/16,1)
T = [[4616,−39,−1250], [−39,55069,−1519], [−1250,−1519,6499]] / 8192
B = D T⁸ D.
```

This adapted rational `B` is not the integer `B` printed in the original proof.
The full canonical target can be refuted by any valid PD pair, so that change
does not weaken the target. Colbrook retains credit for the original
counterexample and method; the rational adaptation/formalization is identified
with George Stepaniants, the approved Department of Computing and Mathematical
Sciences, California Institute of Technology affiliation, and AI assistance.
No original-witness identity, new historical-priority claim or George email is
introduced. The original residual-to-root lemma, original integer `B`, the
approximation `S` and the source's 10900/10200 thresholds are explicitly outside
the claims of this adapted formalization.

My independent [Fraction reconstruction](statement-referee-1-evidence/reconstruct.py)
parses the nine entries of the original rational `R` directly from the immutable
Colbrook TeX. It proves that each proposed numerator is strictly within one half
of `8192 R_ij`, so it is the unique nearest integer without needing a tie rule.
It then recomputes the proposed matrices using generic sequential multiplication
and permutation determinants, without importing the author's reconstruction or
any submitted verifier. Its actual checks include:

- The numerator's leading minors are exactly `4616`, `254196983`, and
  `1555181999141`. The displayed rational LDL identity holds, its triangular
  factor has determinant one, and all three pivots are positive.
- Both inverse identities for `D` hold; the diagonal proposals satisfy
  `F⁸=A`, `F⁴=D`, `F⁵=E` and `FD=E` exactly.
- All entries of `T²,T⁴,T⁸`, adapted `B`, `N=ETDB` and `AB` are recomputed.
  The normalizing identity `D⁻¹BD⁻¹=T⁸` holds, and `B` is different from the
  original printed integer matrix. Direct principal-minor diagnostics for
  adapted `B` are positive as well.
- The real vector `(0,4/5,−3/5)` has squared Euclidean norm exactly one.
  The actual trace, tested coordinate and sum of all nine squared `AB` entries
  have strictly positive exact margins for
  `trace(B)<4⁸`, `44000<Re(Nv)_0`, and `‖AB‖F²<10500²`.

The full exact values and margins are retained in
[reconstruction.json](statement-referee-1-evidence/reconstruction.json). No
spectral root, eigenvalue, operator norm or singular value is evaluated
numerically by this diagnostic. These checks validate the proposed finite
statements; the later Lean proof still must establish them on the actual
Definitions.

## Analytic reduction and remaining proof obligations

The proposed route is mathematically sound and preserves factor order. With
`Y=B^(1/8)` as the **actual** CFC root, positivity must first give the principal
identities. For the adapted input the normalized eighth root is `T`, giving
`A#_(1/8)B=DTD`. Multiplying the actual left product on the right by `Y` gives

```
L Y = F D T D B^(7/8) Y = E T D B = N.
```

Only powers of the same matrix `B` are combined; neither `T` nor `Y` is commuted
past `D`. Each power identification, `Y.PosDef`, `Y⁸=B`, the product identity and
the bound `‖Y‖₂<4` is a conclusion of `witness_principal_powers`. None is hidden
inside a hypothesis, definition field or supplied certificate.

For the root bound, the required reasoning is
`‖Y‖₂⁸=‖Y⁸‖₂=‖B‖₂≤Re tr(B)<4⁸`; positivity supplies the norm-power and trace
bridges, and nonnegative norms give the strict root comparison. The pinned
Mathlib `IsSelfAdjoint.norm_pow_two_pow` at index three is directly relevant to
the eighth-power norm identity. Its use must be with the genuine L2 operator
norm and an explicit conversion to the project's Euclidean-map norm.

The unit-vector and generic norm bounds then give
`44000<Re(Nv)_0≤|(Nv)_0|≤‖N‖₂≤‖L‖₂‖Y‖₂`. If `‖L‖₂≤11000`, the last expression
is at most `44000`, a contradiction. The Frobenius bound yields
`‖AB‖₂<10500`. The stipulated LeanCert point certificate `10500<11000` can then
be consumed in the actual strict norm comparison, transported to singular values
by the generic first-value equality, and used to negate the first mandatory
prefix inequality of the full conjecture.

This gate does not treat that plan as a completed proof. All eight exports,
especially actual singular-value/operator-norm equality, the trace/root bound
and the noncommuting `LY=N` identity, remain mandatory implementation work.
Final reviewers must confirm that the kernel LeanCert certificate participates
in the resulting proof, rather than only appearing in an unused lemma.

## Fresh checks, standards and reproducibility

I compiled Definitions, Challenge and my own actual-declaration inspector in
sequence into a fresh isolated object prefix. The old project build directory
was excluded from `LEAN_PATH`. All three commands exited zero; Definitions and
inspection emitted no warnings, and Challenge emitted exactly its eight
intentional placeholder warnings. All **23 definition** kernel assertions and
actual transitive axiom reports contain exactly `propext`, `Classical.choice`
and `Quot.sound`. No Challenge theorem is advertised as proved by those checks.
No implementation `Proof.lean` or `Solution.lean` existed before or after review.

This was local macOS arm64 using Lean 4.33.1. All ten dependency checkouts are
clean, including untracked files, and exactly match their pins. Mathlib is
`0df444a360eaa60ab8c11dca51a86af692955474`; LeanCert is
`621a43d7cf21f87872392a01e874f2f1dbddc926`. Existing pinned dependency object caches
were reused. This is neither a full dependency-source rebuild nor Linux
Comparator/default-kernel execution.

I applied the relevant correctness, scope, generality, reuse, proof-planning and
attribution criteria from the repository's Tau Ceti adaptation. The rubric
revision is `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`, with the previously read
rubric bytes rechecked against immutable Git tree blobs. Relevant actual Mathlib
singular-value, spectral, CFC and norm APIs were read and searched. The package
keeps one canonical target, uses the library's actual objects, and reduces the
calculation to exact small matrix arithmetic, one vector and a scalar sign
comparison. It does not introduce speculative generalized machinery or an
unproved neighboring result. Tau Ceti's external roadmap-admission rules are
not imported, and no official Tau Ceti endorsement is claimed.

Reproduce this local review's checks from the project directory with:

```
python3 reviews/statement-referee-1-evidence/fresh_review.py
python3 reviews/statement-referee-1-evidence/reconstruct.py
python3 reviews/statement-referee-1-evidence/audit.py
```

The evidence directory retains exact commands, logs, environment and object
hashes, all frozen source/pin identities, complete declaration signatures,
actual elaborated definitions, independent rational calculations, primary-source
scope and inspected-library/rubric hashes. Its `EVIDENCE-MANIFEST.json` binds this
report and the retained artifacts. Only this report and that evidence directory
were written. No mathematical statement, source attribution, canonical page,
status, ID, configuration or pin changed; no proof implementation, commit, push
or publication was performed.
