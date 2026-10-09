# KE-03 independent statement review 1

**Phase:** pre-proof mathematical statement and computational-model review.
**Reviewer:** OpenAI Codex AI agent `/root/choose_algebra`.
**Verdict:** **APPROVE**, specific to the source bytes recorded below.
**Canonical repository revision:** `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`.

I did not author the definitions, Challenge, or any KE-03 proof. Earlier design
feedback identified review criteria; it was not an approval. I independently
read the actual definitions and signature, the canonical problem and complete
informal proof, `NUMERICAL_TARGETS.md`, and the review protocol. I inspected the
relevant pinned Mathlib definitions rather than relying on names or author
descriptions. No required statement correction was found.

## Exact reviewed bytes

Paths in the following table are relative to this Lean project unless prefixed
with `repo:`. Hashes are SHA-256 of the exact file bytes.

| File | Bytes | SHA-256 |
|---|---:|---|
| `repo:docs/lean/REVIEW.md` | 3110 | `d967ddce620d4e754e2f9c25548f30cb537f76f4ddcf8ecf2574945bcd332553` |
| `../README.md` | 4523 | `6e2f296520b00a62662c156f84cba6d69455f8caffbf57067ee888de3a5dfbc2` |
| `../solution.md` | 9401 | `e8696c97fbb703463f2fc5b8f146a8ac06f058176ee7c979711ddd620e4e1b60` |
| `../solution.tex` | 11520 | `123aeda0ac5bc2fb7eee61ab9a7b8baf658f5b624dcd61019afde00cddbf1a8e` |
| `NLA/KE03/Definitions.lean` | 7086 | `5a45dcdf2bab4b960a7246389207e458eada09164ee67fbb2b35649b60c35b4b` |
| `Challenge.lean` | 230 | `d11ca6c70fcfe131440a9e2e6d7b1db6ec71efdcd95ba7d2037cc77149487ab4` |
| `NUMERICAL_TARGETS.md` | 6965 | `af00fd02da11615ee052f60875c4f65601e8ca8925f7354943fd930dedf0ee31` |
| `comparator.json` | 224 | `a0b9bed366262d38f58fe4eebdf182f5d3202ad5425b8e2b08b33925dcb87018` |
| `lakefile.toml` | 297 | `0773d39ded4a3aab0fb35a648c0db2f71bb3efbc4fcdc90e565b294eb8e1e873` |
| `lean-toolchain` | 25 | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lake-manifest.json` | 3540 | `11d76d4ad2d442a8f1bfbbbd97899ca08ac6d8912d39dd3436348d5a98aeb23b` |
| `verification/statement-build.log` | 185 | `4e9099da29484dd32bc4eec603c0a8dde952a7409bad8f1664b91127b15183f3` |

The complete informal proof I read is `solution.md`; the adjacent TeX hash was
checked for source identity, without claiming a separate rendering audit.

## Full-target fidelity

`complete_query_algorithm` asserts a universal positive real constant `C` for
the explicitly defined `runAlgorithm`. Thus the algorithm is fixed before the
matrix is quantified, and the quantifiers cover every positive dimension,
every supplied real `K >= 1`, every `0 < ε < 1/2`, and every admissible complex
matrix with positive actual spectral radius. Fixing exponents to one and two
is a sufficient affirmative answer to the original existence question.

`Conditioned` supplies a two-sided inverse pair and an actual diagonal
similarity with the stated condition bound. It neither supplies that pair to
the algorithm nor adds a spectral-gap, simple-spectrum, normality, or scale
assumption. `Vec` is `EuclideanSpace ℂ (Fin n)`. I checked
`Mathlib/Analysis/InnerProductSpace/PiL2.lean`: this is the finite L2 space, with
squared norm equal to the sum of squared coordinate norms. I checked
`Mathlib/Analysis/CStarAlgebra/Matrix.lean`: `toEuclideanCLM` is the Euclidean
matrix action, with `toEuclideanCLM_toLp` giving ordinary matrix-vector
multiplication. `opNorm` consequently denotes the intended induced norm.

`Eigenvalue` requires a nonzero actual eigenvector. `Successful` uses one
eigenvalue for both inequalities, with the correct factors and weak endpoints.
`radius` is a real supremum of these eigenvalue norms. Under the input promise,
the later proof must establish nonemptiness and boundedness and identify this
supremum with the finite maximum over the diagonalizer's list; these facts are
not supplied as extra input hypotheses. The definition is mathematically
appropriate for the promised finite-dimensional matrices, including repeated
eigenvalues and dimension one.

The success law is the cardinality ratio of a predicate on the entire finite
seed space. It is not conditioned on success, a nonzero starting vector, or any
information about the spectrum. `SolvesKE03` separately requires termination
for every seed and a deterministic query bound for every returned output.
The probability threshold is exactly `99/100`. There are no certificate or
favorable-event premises hiding the desired conclusion.

## Computational meaning and oracle accounting

I inspected `Mathlib/Data/Part.lean`. A `Part` contains a domain proposition
and a value when that proposition holds; membership entails domain and value
equality. Its `map` preserves the domain and its `bind` requires termination
of both stages. Accordingly, the domain clauses in `SolvesKE03` really require
termination of the degree and, when reached, radius and mesh searches.

`searchNat` denotes exhaustive sequential search with result `Nat.find`. It
does not branch on the decidability of its existential domain. Every predicate
actually passed to it is an explicit finite combination of arithmetic and
comparisons. A successful least trial has a finite index, so finitely many
such tests suffice. This is an appropriate denotational presentation of the
original exact-real arithmetic model; it does not claim that classical Lean
real comparison yields an executable floating-point program.

I also inspected the pinned definitions of `Nat.log` and `Nat.unpair`.
The former is fuel-recursive natural arithmetic; the latter uses the integer
square root and finite arithmetic. These do not grant real logarithm or real
root primitives. Natural quotient, integer square root, and finite list
operations can themselves be performed by finite arithmetic and comparisons;
their scalar running time is outside the target.

The concrete `runAlgorithm` supplies the oracle only to `history`. Each
recursive history transition appends one oracle response; `QueryTrace`
formalizes precisely that transition at one extra query. `finish`, radius
search, mesh construction, shifted-power computation, and selection receive
only the stored finite list. In particular, no helper has uncharged access to
matrix entries, an adjoint product, an inverse, or an eigenvalue operation.
The returned count is the same degree used to construct this history.

History is stored in reverse power order. The `m-j` lookup in `shiftedPower`
therefore refers to `A^j b`, as required by the binomial expansion. The finite
fold's initial candidate `1` belongs to the candidate list, and strict
comparison retains an existing maximizer on ties. Degree search always returns
a positive natural number. A zero squared norm exits before radius search;
the full theorem must still prove all-seed termination of every remaining
branch. No real root, real logarithm, norm oracle, or spectrum appears in the
runtime predicates. Real and imaginary squared coordinates compute the norm
comparison arithmetically.

## Independent check of the integer-grid deviation

This change from the source is mathematically sound and does not weaken the
target. Write `N = gridSize n`. For positive `n`, the defining floor logarithm
gives `1024*n < N <= 2048*n`. Thus `N` and the seed-space cardinality `N^n` are
powers of two, with a fixed finite fair-bit sampler independent of `A`.

For a nonzero inverse-diagonalizer row `w`, choose a coefficient `c` of maximum
modulus. Fix every other integer seed coordinate. If two distinct integer
values both gave `|ct+d| < |c|/2`, their outputs would be less than `|c|` apart
by the triangle inequality, but at least `|c|` apart because the integers
differ by at least one. Hence each fiber has at most one bad coordinate.
Union counting over rows gives failure probability at most `n/N < 1/1024`.
The strict bad-event inequality leaves the required weak lower bound on its
complement, including equality cases.

On that simultaneous event, `|w b| >= |c|/2 >= ||w||/(2*sqrt(n))`.
The identity `w V = e_i` gives `||w|| >= 1/||V||`. For any polynomial, the
similarity calculation therefore gives a lower norm bound of
`max |p(λ)| / (2*sqrt(n)*K)`. Deterministically,
`||b|| <= sqrt(n)*(N-1)`, giving the upper bound
`K*sqrt(n)*(N-1)*max |p(λ)|`. Both are covered by
`F = 2*n*N*K`. The event is independent of the polynomial, so the estimates
cover adaptive shifts from the same history. Since `N <= 2048*n`, `log F`
has the required universal `O(1 + log(n*K))` bound.

The mesh uses `q >= 32/ε`, so its parameter spacing `2/q` is at most `ε/16`.
Both stereographic semicircles and endpoints are included. Their speed bound
of two yields coverage at least as fine as the required `ε/8`. The positive
rational enumeration covers all positive rationals; for positive `S` and
positive degree, the acceptable radius interval has positive length because
`η > 0`. This supports the stated all-seed termination obligation without
introducing a real-root instruction. These checks establish plausibility and
fidelity of the boundary, not the missing formal lemmas.

## Mechanical evidence and remaining gates

I inspected `verification/statement-build.log`: the build reports success for
2401 jobs, including `NLA.KE03.Definitions` and `Challenge`. Its sole displayed
warning is the intentional Challenge `sorry`. I did not independently rerun
this build. The toolchain is Lean `4.33.1`; both the manifest and the actual
Mathlib checkout identify commit
`0df444a360eaa60ab8c11dca51a86af692955474`.

Comparator configuration selects separate `Challenge` and `Solution` modules,
the exact advertised theorem, no definition holes, and only `propext`,
`Classical.choice`, and `Quot.sound`. I did not run Comparator or a transitive
axiom audit in this statement phase. This report approves the frozen statement
and reviewed computational model only. The Challenge placeholder establishes
no mathematics, and the final proof, final independent reviews, axiom audit,
and sandboxed verification remain outstanding.
