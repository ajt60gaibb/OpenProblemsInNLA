# TR-15 independent statement review — referee 2

**PASS for proof implementation against the frozen seven-export statement
package.** The definitions and complete target match the retained canonical
problem and Colbrook counterexample. This is approval of what must be proved,
not a claim that a Lean proof or Linux verification already exists.

Reviewer: coordinating agent `/root`, independent of statement author
`/root/leancert_examples`, 12 September 2026. I read the full canonical page,
the full retained Colbrook manuscript, every proposed definition and Challenge
signature, the numerical specification and source correspondence. I separately
reconstructed the tensor contractions with exact integer arithmetic and
freshly elaborated the statement environment. No candidate mathematical bytes
were altered. This applies relevant Tau Ceti statement-fidelity criteria; it is
AI-agent review, not human peer review or Tau Ceti endorsement.

Mathematical counterexample: Matthew J. Colbrook, Department of Applied
Mathematics and Theoretical Physics, University of Cambridge. Formalization:
George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA, with substantial
AI-agent assistance. No mathematical authorship transfer is implied.

## Reviewed inputs

The 19 candidate inputs and six retained original sources in
`reviews/statement-freeze.json` were independently rehashed, and all original
sources compared byte-for-byte with upstream revision
`8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`. They are unchanged.

| Boundary | SHA-256 |
| --- | --- |
| Statement freeze | `302e403878a0ceff29cac2b516a97fbc67ce372f7b8526e0e6c0fe4c6ff9eb69` |
| `NLA/TR15/Definitions.lean` | `63b8767fd19148b269f6e4041d464f0de5dc64cac82e1448fee43115bed55379` |
| `Challenge.lean` | `6778940f8f0f645fc6be0c57f1fb8f67791e0c67c896074651bca9cada491428` |
| `NUMERICAL_TARGETS.md` | `6851bb94fb8f6049980113b4df9a1346bd3ed9549f66dd74b2b1f6a5ee947cd6` |

Neither `NLA/TR15/Proof.lean` nor `Solution.lean` exists at this gate. The only
proof terms in Definitions establish the finite index bound, successor-index
bound, and the equality used in the generating-vector length cast. They do not
assert a contraction equation, positivity property, root or eigenpair.

## Full mathematical target and tensor semantics

`InheritanceConjecture` retains every odd m ≥ 3, every q ≥ 2 and n ≥ 2, every
real generating vector of length qm(n−1)+1, and the original implication about
absence of negative real H-eigenvalues. It does not restrict q to even values,
require a positive-semidefinite associated matrix, or assume the existence of a
lower eigenpair. The witness may have even higher order because one admissible
instance refutes a universal conjecture; this does not narrow the conjecture.

The tensor is the actual finite array on all ordered index tuples. Zero-based
indexing changes the canonical one-based sum minus the order into the ordinary
sum, with identical generator entries. `generatorIndex` proves a real finite
bound and uses no default entry. The lower tensor's cast only identifies equal
lengths; it neither permutes generators nor changes entries. Both tensors use
the same h with the exact prescribed orders and dimensions.

I inspected the elaborated `contraction`: it sums over every ordered function
`Fin (s−1) → Fin N`, prepends exactly the uncontracted coordinate, and multiplies
one signed real coordinate per slot. No norm, absolute value, factorial divisor
or extra multinomial weight is inserted. The actual H-eigenpair equations use
ordinary natural powers of signed real coordinates and require a nonzero real
vector. Thus the proposed array model matches the complete source definition,
without needing an unrelated tensor-product construction.

The total definitions at order zero or dimension zero are irrelevant to the
original admissible domain: lower order is at least three, higher order at least
six, and both dimensions are positive. There is no endpoint admitted to the
conjecture by this totalization. `HasNoNegativeHEigenvalues` quantifies every
real pair and requires eigenvalue ≥ 0, exactly the absence of a negative real
H-eigenvalue. An eigenpair-existence theorem is an additional conclusion, not
an unproved premise that makes the counterexample conditional.

## Independently reconstructed obligations

The exact common vector is (2,0,1,0,2,0,−1), at m = 3, q = 2, n = 2. Both
generating lengths are seven. Independently expanding all 27 lower entries
from the one-based source indexing reproduces every coefficient of the three
proposed contraction polynomials. In particular, the first is

```math
(x_0+x_2)^2+x_0^2+x_1^2+x_2^2.
```

For every nonzero real vector this is strictly positive: at least one of the
three coordinate squares is strictly positive. An actual H-eigenpair therefore
has eigenvalue times x₀² strictly positive, forcing x₀ ≠ 0 and eigenvalue > 0.
This is a valid universal proof obligation over all real eigenpairs. No spectrum
enumeration, generic root-solvability assumption or positivity sampling is used.

My independent reconstruction also evaluates all 64 upper entries in its two
component sums. With v = (0,1), the sole surviving contracted tuple in each
component is (1,1,1,1,1), giving exactly (h₅,h₆) = (0,−1). This equals
−1 times the coordinatewise fifth powers of v, and v is nonzero. The proposed
negative pair is thus for the actual generic upper tensor, not a different
array or a separately stipulated eigen-equation.

For the nonvacuity export, substituting (1,0,t) and eigenvalue 2+2t+2t² makes
the first two equations automatic. Subtracting the third actual contraction
from the required third right-hand side gives coefficients (−1,−4,3,2,2),
exactly `rootPolynomial`. Its values at zero and one are −1 and 2. The actual
pinned `intermediate_value_Ioo` theorem, whose source and type I inspected,
applies to this continuous polynomial and places a zero strictly inside (0,1).
No endpoint ambiguity or root approximation remains. The vector has first
coordinate one, so its nonzero requirement is automatic once the equations are
proved. This advertised extra conclusion is feasible without root isolation.

These reconstructions are finite exact transcription diagnostics. The universal
lower contraction formulas, all-eigenpair positivity, IVT existence, original
admissibility and full conjecture negation still require Lean proofs. A passing
Python check is not treated as their certificate.

## Computation plan and trust boundary

I approve using only the first lower slice for the positivity argument and
the sole nonvanishing upper tuple for the negative eigenpair. Full eigenvalue
computations or an interval grid would add unnecessary work. Small exact
finite sums and polynomial identities suffice; a real IVT theorem supplies
existence without numerical root isolation.

The planned LeanCert kernel point certificate for −1 < 0 has an actual role in
the negative H-eigenpair and final contradiction. It must be retained in those
proof dependencies. Use explicit kernel mode with no automatic native fallback,
and only `propext`, `Classical.choice`, `Quot.sound` transitively in final
theorems. The final review must check that the certificate is consumed, the
actual tensor sum is expanded correctly, and the original universally
quantified conjecture is negated.

## Independent local evidence and next gate

I freshly elaborated Definitions and Challenge in a separate prefix, then
compiled my independent inspection against them. All three commands returned
zero; there were exactly the seven intended Challenge placeholders and no
other warnings. The actual elaborated tensor, contraction, H-eigenpair,
parameter, witness and full-conjecture definitions were inspected. All ten
dependency checkouts are clean at the manifest pins, including Lean 4.33.1,
Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`. This macOS development check reused
pinned dependency artifacts; it is not Linux Comparator or a full dependency
source rebuild.

[Independent evidence](statement-referee-2-root-evidence/manifest.json) retains
the exact driver and commands, raw logs, source identity and pin checks,
separately written exact reconstruction and output, and read-library hashes.
The inspection log SHA-256 is
`e7f070fdc58046c8a1bad2bd87f5140dcefdc503ce66d1564adc7629bfae6fdf`.
Comparator is configured for exactly the seven reviewed names, no definition
exceptions, and the standard three permitted axioms.

Proof implementation may start once the other independent statement approval
is also recorded. Completed proofs must receive two independent final reviews
and actual Linux Comparator/default-kernel checks before canonical promotion.
No problem ID, original target, canonical status, Git commit, push or PR was
changed by this statement review.
