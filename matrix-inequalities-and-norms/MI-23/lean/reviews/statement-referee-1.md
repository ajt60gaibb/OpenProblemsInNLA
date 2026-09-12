# MI-23 independent statement referee 1

**APPROVE the frozen eight-export statement boundary. No mathematical correction requested.**

Reviewed on 12 September 2026 by OpenAI Codex agent `/root/leancert_examples`.
I did not author or edit these mathematical statements. This is a statement-fidelity
approval before implementation, not a completed proof or Linux verification claim.

## Exact boundary and sources

| Frozen file | SHA-256 |
|---|---|
| `NLA/MI23/Definitions.lean` | `1ca2386528fc7ff944f84088842f62c5f33a38f14cde7ee8127972be29696def` |
| `Challenge.lean` | `283bca1ced50d7953f9946629c24e99f944d81095f9c822fbb3b58a44e01e189` |
| `NUMERICAL_TARGETS.md` | `2f8e41d440d3e24732a1c2b70c0710ad0d88367c2aac7979141959a8d8df25ee` |

I read the full canonical README, complete Colbrook `solution.tex`, source attribution
note, all definitions, all eight Challenge declarations and the numerical plan.
The canonical and complete TeX sources are byte-identical to revision
`8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`, with hashes
`9edc47646606cc1a4317777b4556652038bf5f8ccdd96b9917ab902767c35fb5` and
`a8eb6660e05afbafa9e376d1354d24f97cc0c25debd022e540e11859628b9552`, respectively.
All 20 recorded frozen/source inputs remained unchanged during my review.

I independently retrieved [Ghabries–Abbas–Mourad–Assi, arXiv:2105.13356v1](https://arxiv.org/pdf/2105.13356v1),
checked the log-majorization definition on page 2, and visually checked Conjecture
2.1 on page 6. The exponent order and real parameter ranges agree. That paper
writes semidefinite inputs, while the retained canonical target explicitly uses
positive definite complex matrices; the formalization preserves that canonical
scope and states this distinction. It makes no separate claim about singular-input
negative powers. The external PDF remains outside the repository; its exact hash
and a paraphrased source mapping are retained in
[primary-source-check.json](statement-referee-1-evidence/primary-source-check.json).

## Full target and actual ordered eigenvalues

`GeneralizedGeometricMeanConjecture` quantifies over every `n ≥ 1`, every pair of
complex positive definite matrices, and all real `r,s,p,t` with `p ≥ 1`,
`0 ≤ t ≤ 1`, and either `(r,s ≥ 1)` or `(r,s ≤ 0)`. All endpoints, negative
exponents and nonrational exponents remain included. All real powers are genuine
`CFC.rpow`; `generalizedMean`, `leftProduct` and `rightProduct` retain the exact
noncommuting factor order and exponent `p*(r+s-1)` from the source.

`orderedEigenvalues` takes the actual characteristic-polynomial **root multiset**,
maps it to real parts and sorts it using `≥`. This is not a set, so repeated
roots are retained. I checked Mathlib's actual `Multiset.sort`, `sort_eq`,
`length_sort` and `pairwise_sort`: sorting preserves the entire multiset and its
cardinality. I also checked the genuine Hermitian spectral theorem APIs
`roots_charpoly_eq_eigenvalues₀` and `sort_roots_charpoly_eq_eigenvalues₀`; the
latter's descending relation is exactly the relation used here.

Mapping to real parts could be unfaithful for arbitrary matrices, but the generic
`product_eigenvalue_semantics` export is required to prove **every** relevant
product has length `n`, strictly positive entries, descending order, the full
original root multiset after re-embedding into complex numbers, and complete
product equal to its actual determinant. The reverse multiset equality prevents
any nonreal root or algebraic multiplicity from being hidden by the map. These
facts are conclusions, not extra assumptions in the universal target.

The same generic export must prove an explicit two-sided inverse and similarity:
with `R=Y^(1/2)` and `Rinv=Y^(-1/2)`, the positive matrix `S=R*X*R` satisfies
`R*(X*Y)*Rinv=S` and has the same characteristic polynomial. This identity has the
correct orientation. The `positive_powers_and_means` export proves positivity
for **all real** exponents, so it covers every factor used in both parameter
regions. Mathlib's actual `Matrix.isStrictlyPositive_iff_posDef` and CFC inverse
power laws supply the appropriate analytic APIs without adding a hidden
invertibility hypothesis to the original positive-definite target.

`LogMajorized` contains equality of lengths, all nonempty proper prefix-product
inequalities, and equality of complete products. Positivity and ordering are
separate proved semantic obligations of the actual matrices, not replacements
for those conditions or strengthened premises. For `n=1`, only complete-product
equality remains, as in the original definition. At the `n=3` witness, the first
prefix is included. Positive list length makes the zero default in
`largestEigenvalue` irrelevant; the norm is never defined to be an eigenvalue.

## Analytic bridges and exact witness

The generic `squared_product_largest` theorem must identify the first entry of
that actual list with `operatorNorm(X*Y)^2` for every positive-definite `X,Y` in
positive dimension. The correct similar positive matrix is
`Y*X^2*Y=(X*Y).conjTranspose*(X*Y)`.
Together with the genuine C-star norm identity and the spectral theorem, this
justifies the proposed bridge for a generally non-Hermitian product. I inspected
`Matrix.toEuclideanCLM`: it is a star-algebra equivalence with continuous linear
endomorphisms of complex Euclidean space. The printed norm term carries the
actual Euclidean `p=2` structure, and the natural witness powers use
`Matrix.semiring`, not pointwise exponentiation.

The generic norm-bound export uses every complex squared entry modulus and the
sum over **all** entries. It must prove both the entry lower bound and the full
Frobenius upper bound on the squared Euclidean operator norm. These are proof
obligations rather than assumed numerical estimates.

I independently reconstructed the entire rational witness with Python `Fraction`,
using ordinary exact matrix multiplication and a determinant recursion. The
proposed LDL* factorization is exact: `det(L)=1`, the three positive pivots are
`2,49/2,150/49`, and the leading principal minors of `T` are `2,49,150`.
Both orders of `D*Dinv=I` hold, and `Dinv*B*Dinv=T^8` holds exactly.
All nine entries of `GH` and `AB`, and all nine squared terms of the Frobenius
sum, were reconstructed independently. They give

```
(GH)[0,2] = 1260589125202/9,
FrobeniusSquared(AB) = 2009446159144992718181231562721/107495424,
|(GH)[0,2]|^2 - FrobeniusSquared(AB)
  = 99434824489435745411095588895/107495424 > 0.
```

The witness parameters `r=s=1`, `p=2`, `t=1/8` satisfy every canonical premise
and avoid the known narrower interval `[1/4,3/4]`. The true spectral identities
`(T^8)^(1/8)=T` and `(T^8)^(7/8)=T^7`, all six positive-definiteness claims,
and both actual generalized-mean identities remain Lean conclusions. I checked
that the pinned CFC composition and natural-power APIs match these mathematical
reductions; the rational script does not claim to establish them.

Consequently the proposed eight exports cover the necessary semantics, exact
witness and strict norm gap, actual largest-eigenvalue violation, failure of the
complete log-majorization, and unconditional full conjecture negation. No witness
fact, eigenvalue formula, convergence assumption, certificate, or norm inequality
has been inserted as an unproved hypothesis. The one planned explicit kernel
LeanCert point certificate must be consumed by the final strict comparison.

## Fresh elaboration, review standards and gate

I freshly compiled Definitions and then Challenge to a separate artifact prefix,
excluding the original project `.lake/build/lib/lean` from `LEAN_PATH`. An
independent inspection module then read the actual types, instances and relevant
Mathlib APIs from those fresh artifacts. All three commands exited zero;
Definitions and inspection had no warnings, and Challenge had exactly eight
intentional placeholder warnings. The two inspected definitions depend only on
the standard three axioms; the inspected unproved Challenge theorem correctly
reports `sorryAx` at this pre-proof stage.

- [Fresh commands/results](statement-referee-1-evidence/fresh-checks.json): `13cec16f9708343a249008ff8a89737f4f202727dbcd0e98cdbb06e702966db1`.
- [Actual full inspection](statement-referee-1-evidence/inspection.log): `24cd52d9652e4b76cf24e0ea10daee392264895de8bb6d2222f549a92845a919`.
- [Independent rational reconstruction](statement-referee-1-evidence/rational_check.py) and [exact results](statement-referee-1-evidence/rational-check.json).
- [Before](statement-referee-1-evidence/inputs-before.json)/[after](statement-referee-1-evidence/inputs-after.json) identities, [library hashes](statement-referee-1-evidence/library-hashes.json), and [dependency checks](statement-referee-1-evidence/dependencies.json).

All ten actual dependency checkouts match the manifest and have clean tracked
worktrees. Matching compiled dependency artifacts were reused. This was local
macOS statement elaboration, not a full dependency rebuild, completed Lean
proof or actual Linux Comparator run.

I applied the recorded Tau Ceti correctness/faithfulness, scope, reuse and
attribution rubrics at `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`, adapting
scope to the permanent MI-23 target rather than Tau Ceti's own roadmap. The
actual Mathlib spectral, sorting, positivity and CFC APIs are reusable; the
separate scope-mapping exports expose the mathematical boundary instead of
assuming its hard prerequisites. The original proof remains attributed to
Matthew J. Colbrook. George Stepaniants receives formalization credit with his
full Caltech Department of Computing and Mathematical Sciences affiliation and
no email. No official Tau Ceti or external human endorsement is claimed.

There was no Proof or Solution implementation at the time this approval was
frozen. Implementation still requires the second independent statement approval.
Later proof reviews must check all eight exports, the complete ordered-root
semantics and retained kernel certificate, followed by standard-three-only axiom
checks and actual Linux Comparator publication gates. I changed no mathematical
source, canonical file, status, commit or remote state.
