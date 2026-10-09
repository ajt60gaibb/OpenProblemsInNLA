# KE-03 independent statement review 2

- Phase: pre-proof statement and computational-model review.
- Date: 2026-09-28.
- Reviewer: OpenAI Codex AI agent `/root/environment`.
- Independence: this reviewer authored neither the KE-03 definitions nor any
  KE-03 mathematical proof. This is an AI-agent review, not human peer review.
- Verdict: **APPROVE**, specific to the source bytes recorded below.

## Reviewed sources and hashes

The canonical source revision is
`80c0e3e638b2f26dcb3a00353651fc3d2215dd65`. I read the canonical README and the
complete adjacent informal solution, and independently checked their hashes
against `git show` at that revision. I also read `docs/lean/README.md` and
`docs/lean/REVIEW.md` and inspected the actual boundary definitions rather than
relying on the author’s prose or prior informal PASS review.

| File | SHA256 |
| --- | --- |
| `../README.md` | `6e2f296520b00a62662c156f84cba6d69455f8caffbf57067ee888de3a5dfbc2` |
| `../solution.md` | `e8696c97fbb703463f2fc5b8f146a8ac06f058176ee7c979711ddd620e4e1b60` |
| `../solution.tex` | `123aeda0ac5bc2fb7eee61ab9a7b8baf658f5b624dcd61019afde00cddbf1a8e` |
| `NLA/KE03/Definitions.lean` | `5a45dcdf2bab4b960a7246389207e458eada09164ee67fbb2b35649b60c35b4b` |
| `Challenge.lean` | `d11ca6c70fcfe131440a9e2e6d7b1db6ec71efdcd95ba7d2037cc77149487ab4` |
| `NUMERICAL_TARGETS.md` | `af00fd02da11615ee052f60875c4f65601e8ca8925f7354943fd930dedf0ee31` |
| `comparator.json` | `a0b9bed366262d38f58fe4eebdf182f5d3202ad5425b8e2b08b33925dcb87018` |

The TeX hash was checked for source identification; my complete mathematical
source reading was of `solution.md`. The project pins Lean 4.33.1 and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.

## Fidelity and quantifiers

`complete_query_algorithm` asserts one universal positive real constant `C`.
Its `SolvesKE03` definition quantifies over every positive dimension, every
supplied real `K ≥ 1`, every `0 < ε < 1/2`, and every complex matrix satisfying
the conditioning and positive-spectral-radius promises. The fixed query
exponents are `a = 1`, `b = 2`, which supplies the original existential
exponents without narrowing the inputs. The theorem requires termination and
the query bound for every seed, and success probability at least `99/100`.

`Successful` requires a single actual eigenvalue to satisfy both the
near-largest-modulus and the complex-distance conclusion. It does not replace
the eigenvalue by a pseudospectral point or merely approximate the radius.
No spectral gap, distinct-eigenvalue, spectral-scale, or favorable-seed
assumption appears. The restriction to positive dimension follows from the
original positive-radius setting.

I inspected the imported definitions of `EuclideanSpace` (`PiLp 2`),
`Matrix.toEuclideanCLM`, and its matrix-vector evaluation equations.
Consequently `Vec`, `act`, and `opNorm` use the stated Euclidean vector norm
and induced operator norm. `Conditioned` gives both inverse identities and
the diagonal similarity, with the product of these operator norms bounded
by `K`. Its witnesses are absent from the algorithm interface.

`Eigenvalue` has the usual nonzero eigenvector meaning. `radius` is the real
supremum of actual eigenvalue norms. The proof must establish the nonempty,
bounded finite-spectrum interpretation from the positive dimension and
diagonalization; the boundary does not assume a radius estimate or provide
spectral data to the algorithm. This is a proof obligation, not a defect or
an extra hypothesis.

## Concrete finite exact computation

The only inputs to `runAlgorithm` are `n`, `K`, `ε`, the vector-query oracle,
and a finite seed. Its computational call graph has one oracle-call site:
each successor of `history` queries the previous first vector, stores the
response, and retains the history. `QueryTrace` charges one query for that
transition, and the returned count is exactly the chosen degree. All
postprocessing receives the finite stored list. There is no access to matrix
entries, diagonalizers, eigenvalues, an adjoint oracle, or a shifted-system
oracle. The indexing of `shiftedPower` agrees with the reversed history:
entry `m-j` supplies `A^j b` to the binomial sum.

I inspected Mathlib's `Part` structure, membership, map, and bind. Membership
in the resulting `Part` asserts termination and the actual returned value;
it cannot identify an arbitrary successful output. `searchNat` denotes the
least successful natural trial, with domain exactly the existence of one.
Although generic `Part` values need not represent effective computation,
every predicate used here is an explicit finite arithmetic comparison. This
concrete least-search construction denotes sequential exhaustive search in
the permitted exact-real comparison model. It does not decide its domain
as a preliminary operation. No unspecified semantic postprocessor occurs
inside its maps or binds.

The positive degree search uses multiplication and comparison. The zero
squared-norm case exits explicitly. The positive-radius search enumerates
positive rationals, and the mesh search returns a positive integer. All
remaining sums, powers, binomial coefficients, list traversals, and finite
maximum comparisons are finite arithmetic. I also inspected the imported
`Nat.log`, `Nat.unpair`, and the natural integer-square-root implementation
used by `unpair`: these are finite integer algorithms, not real logarithm
or real-root primitives. Denominators in positive rationals and circle
points are positive, and the mesh search supplies nonzero mesh size.
Unrestricted finite work between queries permits the potentially slow
rational enumeration. All-seed termination still has to be proved.

The function-valued `Seed n = Fin n → Fin N` with subtype-cardinality
probability is exactly the uniform product law on its finite seed set.
`N` depends only on `n`, is a power of two, and is positive; the denominator
is not an empty-space escape. This law can be sampled using a fixed finite
sequence of fair bits. It does not depend on the unknown matrix or on
query responses.

## Source deviations and remaining obligations

The integer grid and `F = 2*n*N*K` are explicit documented changes from the
source's normalized grid. They preserve the full target. In particular, a
strict disk of radius half a nonzero coefficient's modulus contains at most
one point of an integer-spaced fiber, so the proposed bad-seed count of at
most `n/N` is mathematically sound. The positive-dimension grid bounds
`1024*n < N ≤ 2048*n` retain both the required probability and a logarithmic
query estimate. A largest-coefficient row bound and the diagonalizer norm
bounds suffice with the stated generous `F`. These observations validate
the intended route; they do not substitute for its Lean proof.

The final implementation must prove the simultaneous shifted-power
estimates on one seed event, so that adaptive shift selection remains
covered. It must also prove circle-net coverage, finite-maximality,
all-seed search termination, the actual-spectrum interpretation of
`radius`, and one universal query constant. These facts are not assumed
in the target. The theorem retains the original `0.99` requirement even
though the informal proof advertises a stronger probability.

The Comparator configuration names separate `Challenge` and `Solution`
modules, selects the sole full target, leaves `definition_names` empty,
and permits only `propext`, `Classical.choice`, and `Quot.sound`.
The mathematical-resolution attribution and AI implementation disclosure
in `NUMERICAL_TARGETS.md` retain the source author's role without claiming
human endorsement.

## Mechanical evidence and scope of approval

I independently ran, in this project with the pinned local toolchain:

```text
lake build NLA.KE03.Definitions Challenge
```

It completed successfully (2401 jobs). The only warning was the deliberate
placeholder in `Challenge.complete_query_algorithm`; definitions had no
warning. I also inspected `verification/statement-build.log`, which records
the authors' successful boundary build. At review time the only project
Lean source files were Definitions and Challenge: no mathematical proof
implementation had started.

This approves the frozen statement boundary for proof authoring. It is not
a completed-proof review, a transitive-axiom audit, a Comparator run, or a
fresh Linux sandbox verification. No mathematical target is certified by
this report alone. Any mathematical change to the reviewed boundary must
reopen both statement reviews.
