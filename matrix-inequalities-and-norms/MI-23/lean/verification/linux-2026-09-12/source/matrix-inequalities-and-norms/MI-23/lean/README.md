# MI-23: Lean formalization of the generalized-mean counterexample

The complete eight-export proof has passed local Lean elaboration, 64 distinct
transitive kernel-trust/axiom checks, two independent statement reviews before
implementation, and two independent final proof reviews. It is a reviewed Linux
candidate. Actual Linux sandboxed Comparator, default-kernel replay, negative
controls and operational audit are pending. The canonical problem remains
**Solved**; no Lean-verified repository status is claimed by this candidate.
`Challenge.lean` retains eight intentional statement placeholders and is never
imported by `Solution.lean` or its proof dependencies.

**Mathematical counterexample and informal proof:** Matthew J. Colbrook,
Department of Applied Mathematics and Theoretical Physics, University of Cambridge.
**Lean formalization:** George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA, with
AI-agent assistance.

The target is the [complete canonical MI-23 conjecture](../README.md), with the
[original informal proof](../solution.tex). See [Definitions](NLA/MI23/Definitions.lean),
[Challenge](Challenge.lean) and [numerical targets](NUMERICAL_TARGETS.md). The full
all-real-exponent log-majorization statement includes both original `r,s` regions,
every proper prefix-product inequality and equality of complete products. Actual
characteristic-polynomial roots retain multiplicities and receive explicit
positivity, ordering, reality, similarity and determinant semantic obligations.

The exact witness `A=D²`, `B=DT⁸D` turns the two actual generalized geometric
means into `DTD` and `DT⁷D` after proved CFC identities. It avoids approximating
fractional matrix powers. The only LeanCert computation is one positive
rational gap, checked through Lean's kernel. Generic bounds for the genuine
Euclidean operator norm and the actual largest product eigenvalue connect this
certificate to the original target.

The norm is explicitly `‖Matrix.toEuclideanCLM A‖`. Scoped matrix norms in the
proof use `Matrix.Norms.L2Operator`, with the defining equality
`Matrix.l2_opNorm_toEuclideanCLM`; no entrywise norm is substituted. The exact
certificate is

```
|(GH)[0,2]|² − ‖AB‖F² = 99434824489435745411095588895 / 107495424 > 0.
```

LeanCert checks this sign on a singleton interval in kernel mode. Independent
proof-term inspections confirm that the certificate is retained in the complete
conjecture negation, through the actual operator-norm and eigenvalue bridges.

Build the complete proof with:

```
lake build Solution
```

[Solution](Solution.lean) restates the eight frozen exports.
[Functional calculus](NLA/MI23/FunctionalCalculus.lean) proves positivity and
complete product-eigenvalue semantics; [spectral norms](NLA/MI23/SpectralNorm.lean)
and [norm bounds](NLA/MI23/NormBounds.lean) connect the actual first eigenvalue to
the explicit Euclidean operator norm. [Witness identities](NLA/MI23/Witness.lean)
prove the rational LDL factorization and real-power identities;
[arithmetic](NLA/MI23/Arithmetic.lean) checks repeated-squaring certificates and the
single point inequality; [the final proof](NLA/MI23/Proof.lean) derives the full
conjecture's negation from its first proper prefix-product inequality.

The project pins Lean 4.33.1, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`
and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Its local initial dependency
cache is a separate APFS copy of the already pinned MI-06 dependencies; no MI-06
mathematical module is imported. `comparator.json` reserves the eight reviewed
exports and standard-three-axiom whitelist for later real Linux verification.
[The formalization manifest](formalization.yaml) uses actual schema v0.4 and
records current scope and attribution. [Numerical targets](NUMERICAL_TARGETS.md)
record the original correspondence before implementation.

Both independent phases are retained: [statement referee 1](reviews/statement-referee-1.md),
[statement referee 2](reviews/statement-referee-2.md),
[final referee 1](reviews/proof-referee-1.md), and
[final referee 2](reviews/proof-referee-2.md). Each final report includes its own
fresh source re-elaboration and proof-term inspection evidence. These local
macOS checks reused the ten verified clean pinned dependency caches; they do not
claim full dependency-source rebuilds or an actual project-specific Linux run.

The [proof freeze](reviews/proof-freeze.json) and
[implementation gate](reviews/implementation-gate.json) retain their exact
historical bytes and phase labels. The prior README is preserved unchanged as
[the frozen local-proof README](verification/linux-candidate-2026-09-12/frozen-local-proof-README.md).
Only the current README changes among the 25 proof-freeze inputs; the remaining
24 and all prior reviews/evidence are preserved during packaging. Review follows
the repository's [Tau Ceti adaptation](../../../docs/lean/REVIEW.md) and
[verification protocol](../../../docs/lean/README.md).

The project reuses the campaign's explicit `CFC.rpow`, Euclidean-map norm and
statement-first organization from MI-29/MI-21 and Mathlib's actual APIs. The
shared checker is credited in `tools/lean/NOTICE.md`; Schiffer and Forsythe were
workflow references, not mathematical assumptions. Source authorship, formalization
authorship, independent agent review and eventual mechanical verification remain
distinct. No external human peer review or source-author endorsement is claimed.
