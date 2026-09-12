# MI-23: Lean formalization of the generalized-mean counterexample

The complete proof now builds locally, with all eight public theorems and 64
transitive kernel-trust/axiom checks. Two independent statement reviews approved
the unchanged definitions and theorem types before implementation. Independent
final proof reviews and authoritative Linux sandbox, kernel replay and Comparator
verification are still pending; no Lean-verified repository status is claimed.
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
A publication manifest will be completed after final independent proof review.
The local source elaboration and proof-term inspection records are in `reviews/`;
they are author diagnostics and do not substitute for independent or Linux review.

The project reuses the campaign's explicit `CFC.rpow`, Euclidean-map norm and
statement-first organization from MI-29/MI-21 and Mathlib's actual APIs. The
shared checker is credited in `tools/lean/NOTICE.md`; Schiffer and Forsythe were
workflow references, not mathematical assumptions. Source authorship, formalization
authorship, independent agent review and eventual mechanical verification remain
distinct. No external human peer review or source-author endorsement is claimed.
