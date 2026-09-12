# MI-06 independent statement referee 1

**Verdict: APPROVE the frozen statement boundary. No mathematical correction requested.**

Date: 12 September 2026. Reviewer: independent agent
`/root/solved_statement_inventory`; statement author: `/root/formal_review_standards`.
I did not write or modify the definitions, challenge, or numerical targets. This is
statement review, not approval of an implemented proof or a claim of Lean verification.

## Reviewed identities and source

| Frozen file | SHA-256 |
| --- | --- |
| `NLA/MI06/Definitions.lean` | `a89c6604d36aec8ae3428df7663a2dbb6f2f923b13ca5f7746aaf4f424cb29d2` |
| `Challenge.lean` | `7774d76c9e362c0f808ee4c1fec3b5607359048d5af82d0e99f60b74c52326dc` |
| `NUMERICAL_TARGETS.md` | `792aa98aa94d18d7b49e4e4b66edca89881f1e38cf51c3aacfed8525644509a4` |

I read the full canonical README, complete `solution.tex`, attribution/scope note
`solution.md`, and original independent informal review. Their bytes match Git
revision `02b807770fca860ef810cc048d6849224b8f93e1`; see
[canonical identity evidence](statement-referee-1-evidence/canonical-identity.json).
Canonical README SHA-256 is
`0775b70ff8c7e6228e7a289795584be3455aea4d01d8b5721d5fc338dcae494c`;
the complete TeX source is
`ae2092528c425b8572c73b07678a01307ed3029399d091a670f78a4d28304bd6`.
The formal target is the original universal factor-√2 assertion, settled by the
source's Corollary 1.2. It does not claim the stronger no-finite-constant theorem.

Lean is `v4.33.1`; LeanCert is pinned to
`621a43d7cf21f87872392a01e874f2f1dbddc926`, Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474`. I checked all ten dependency Git HEADs
against the manifest and found clean tracked/untracked status in each package.
All fourteen author-frozen mathematical, configuration, and source inputs remained
unchanged during this review. [Inputs](statement-referee-1-evidence/inputs-before.json),
[post-check identity](statement-referee-1-evidence/inputs-after.json),
[dependency checks](statement-referee-1-evidence/dependencies.json).

## Semantic audit

`DominationConjecture` quantifies over every `n ≥ 1`, every pair of complex square
matrices, and two independently chosen genuine complex unitaries. There are no
Hermitian, real-entry, invertibility, spectral, independence, or precomputed-modulus
hypotheses. The unitary subtype is inhabited and means the conjugate transpose is
the inverse. The elaborated matrix inequality uses `Matrix.instPreOrder`, namely
`(right - left).PosSemidef`, rather than pointwise entry order or an eigenvalue/norm
surrogate. Matrix PSD includes Hermitian symmetry and nonnegative complex quadratic
forms. The scalar is the nonnegative `Real.sqrt 2` embedded into ℂ.

`CFC.abs X` is the actual `CFC.sqrt (star X * X)`, with matrix star equal to conjugate
transpose; `CFC.sqrt` applies the non-unital continuous functional calculus to
`NNReal.sqrt`. `symmetricModulus` takes the arithmetic half-sum of the right and
left moduli. Thus it is the source's arithmetic modulus, including at singular
matrices. The generic `modulus_eq_sqrt` demands positivity as a conclusion for every
complex matrix and requires no spectral assumption.

The six challenge exports preserve these obligations:

| Export | Independent assessment |
| --- | --- |
| `modulus_eq_sqrt` | Actual positive CFC square root and PSD conclusion for arbitrary size/input. |
| `witness_moduli` | All six CFC identifications, three arithmetic averages, and two exact rank-one decompositions are conclusions. No table is assumed correct. |
| `two_vector_orthogonal` | Any two complex vectors in dimension three admit a nonzero orthogonal vector, even when either is zero or they are dependent. |
| `witness_quadratic_bounds` | For every complex unitary pair, a single nonzero vector satisfies both orthogonality constraints and all three homogeneous bounds on the actual CFC quantities. |
| `counterexample` | The fixed rational pair defeats every complex unitary pair in ordinary PSD order. |
| `not_dominationConjecture` | Negates the full original universal assertion, by the admissible dimension-three instance. |

The conjugation in `star a ⬝ᵥ w` is on the correct argument. These are two complex
linear homogeneous constraints on `w ∈ ℂ³`; their map to ℂ² cannot be injective.
`squaredLength w = ∑ᵢ ((Re wᵢ)² + (Im wᵢ)²)` is the squared Euclidean length, and
strict positivity excludes the zero vector. Using a nonzero vector while retaining
this factor is exactly the homogeneous form of the source's unit-vector argument.
The witness may depend on `U,V`, as required to exclude every pair. No default
function norm, normalization assumption, or simultaneous diagonalization is used.

## Independent exact reconstruction

I separately reconstructed the `t = 3/4` inputs with Python `Fraction`, then checked
each proposed positive root using a nonnegative outer-product decomposition and
its square against the actual appropriate Gram matrix. For example,
`rightModulusA = (1/20)(4,3,0)(4,3,0)*` and
`leftModulusB = (1/20)(4,0,3)(4,0,3)*`; the remaining roots are positive diagonal
combinations. All six identities, all three averages, and both stated rank-one
decompositions passed exactly.

The lower-bound remainder is precisely
`symmetricSum - (3/8)I = (3/8)e₁e₁*`. Orthogonality to `U(3,1,0)` and `V(3,0,1)`
removes the positive rank-one terms of the two conjugated decompositions; the
remaining subtracted coordinate projectors are PSD. This gives each upper bound
`(1/8) squaredLength w`. PSD domination would therefore imply
`(3/8) squaredLength w ≤ (sqrt 2/4) squaredLength w`. The scalar gap
`9/4 - 2 = 1/4 > 0` yields `sqrt 2 < 3/2`, contradicting the positive length.
This verifies the mathematical statement plan without replacing any universal
unitary quantifier by sampled unitaries.

The [independent reconstruction script](statement-referee-1-evidence/rational_check.py)
and [results](statement-referee-1-evidence/rational-check.json) are supplementary
exact-arithmetic diagnostics, not a Lean proof or universal proof certificate.

## Fresh elaboration and review scope

I freshly compiled `Definitions` and `Challenge` sequentially into a separate
artifact prefix, excluding the existing project artifact prefix from `LEAN_PATH`.
Two independent inspection files then ran against those newly built artifacts.
All four commands exited zero. Definitions and both inspections had no warnings;
Challenge had exactly its six deliberate `sorry` warnings. The printed types and
instances agree with the source-level review above. The six placeholder theorems
depend on `sorryAx` and the standard three axioms, as expected at this stage; no
implemented theorem has been certified. Dependency caches were reused at the
checked clean pins; this was local macOS elaboration, not fresh dependency building
or Linux Comparator replay.

- [Fresh commands, timings, and hashes](statement-referee-1-evidence/fresh-checks.json), SHA-256 `cbb5d5efceb156c84a16cf8e96cfb942bb810d94c161995fde7840c5b9bcfa49`.
- [Explicit instance inspection](statement-referee-1-evidence/inspection.log), SHA-256 `ec19b2613993cbb707e36fb8615c240fffa1d681f3f365d811d3a85b93a43c3f`.
- [Compact inspection](statement-referee-1-evidence/inspection-compact.log), SHA-256 `1406e9412e91cf25371fc67b5f1013b9acb3a08cd16f3a9110aa29767af33e8e`.
- [Placeholder audit](statement-referee-1-evidence/placeholder-audit.json) and [inspected library hashes](statement-referee-1-evidence/library-hashes.json).

I applied Tau Ceti's correctness, scope, reuse, and attribution angles from recorded
revision `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`, adapting scope to the permanent
MI-06 target rather than Tau Ceti's own roadmap. The definitions reuse actual
Mathlib CFC, PSD order, unitary groups, outer products, and complex norm squares.
The generic two-constraint lemma has a genuine consumer; Mathlib's
`LinearMap.finrank_le_finrank_of_injective` is an available route for its proof.
The manuscript is credited to Matthew J. Colbrook; George Stepaniants receives
formalization credit with the Department of Computing and Mathematical Sciences,
California Institute of Technology affiliation and no email. This is an independent
agent review using adapted rubrics, not an official Tau Ceti or human review.

No `Proof.lean` or `Solution.lean` exists at this review boundary. Implementation
must await the second independent statement approval. Final proof review must
check all six completed exports, standard-three-only dependencies, and substantive
retention of the kernel LeanCert scalar certificate. Linux Comparator, publication,
and canonical status promotion remain later gates. This review changes none of the
mathematical source, canonical files, Git commits, or remote state.
