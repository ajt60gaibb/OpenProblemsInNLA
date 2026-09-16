# MF-12 Lean formalization

George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
AI-assisted formalization. Original mathematical proof: Matthew J. Colbrook,
Department of Applied Mathematics and Theoretical Physics, University of Cambridge.
No contact email is included.

**The complete proof graph has compiled; standalone canonical verification is
pending.** All 28 frozen targets passed actual non-root Linux development
[run 35034380090](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35034380090/job/104599995558)
at revision `a1efcbfc59263b9e5bb00914ee709112348c1e54`. This package preserves
all 19 mathematical source files in that accepted Solution closure. Every final
export passed its LeanCert kernel-trust assertion and reported only standard
axioms; the exact per-declaration sets are retained in `formalization.yaml`.

The full conclusion covers every nonnegative real exponent gamma. A fixed
positive dimension and exactly two distinct fixed real matrices have maximal
norms of all length-n products between fixed positive multiples of n^gamma for
every positive integer n. The norm is the genuine Euclidean operator norm, the
maximum ranges over the complete family-word set and is actually attained, and
the actual nth-root sequence converges to one. The dimension and matrices depend
on gamma, never on the product length.

The proof uses the source's explicit six-dimensional fractional pair and an
ordinary Jordan block for integer exponents. Sparse block identities, finite
Holder, exact rational Bernoulli bounds, integer logarithms and fixed
dimension-factor tensor comparisons avoid interval subdivision and approximate
spectral computations. The sufficient constants are deliberately enlarged;
optional source claims about rational entries, density, sharper constants and
minimal dimension are outside this verification scope.

With the pinned toolchain available, from this directory:

```bash
lake exe cache get
lake build +Solution
```

The default `lake build` also selects Solution. Changing the earlier statement
phase's default target is a configuration transition; it changes no mathematical
source or dependency revision. No local Lean/Lake build or cache download was
performed in preparing this package. A build alone does not replace the stronger
[canonical verification protocol](../../../docs/lean/README.md).

Read [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md),
[Definitions.lean](NLA/MF12/Definitions.lean), and
[Challenge.lean](Challenge.lean) for the complete frozen specification.
Challenge's 28 deliberate placeholders are independently trusted statements and
are never imported by [Solution.lean](Solution.lean). Two independent statement
approvals and actual Linux elaboration preceded proof construction; the
[freeze](STATEMENT-FREEZE.json) and [original records](statement-audit) preserve
that boundary. Their historical draft descriptions remain part of the evidence.

The [complete mathematical source review](reviews/proof-source/MF12-elimination-complete-source/REVIEW.md)
and [actual development acceptance addendum](reviews/proof-source/MF12-elimination-complete-source/development35034380090-addendum/REVIEW.md)
retain their exact original bytes alongside earlier reviews and repairs.
The reviewer also prepared this metadata package without modifying proof code.
A second independent full mathematical reviewer is still required. The reviews
are AI-agent reviews under scoped Tau Ceti criteria, not external human review
or official certification.

[SourceCorrespondence.md](SourceCorrespondence.md) maps every declaration to the
full original target and proof. [formalization.yaml](formalization.yaml) records
all 28 exports and current status. [ACTIVE-SOURCE-MANIFEST.json](ACTIVE-SOURCE-MANIFEST.json)
binds the compiled mathematical bytes; [development evidence](verification/development-35034380090)
and the [packaging transition](verification/packaging) distinguish the tested
shared development revision from this standalone candidate.

Actual standalone Comparator, independent default-kernel replay, required
negative controls and two final source/evidence referee verdicts remain pending.
This package does not change the canonical problem status or any index.
