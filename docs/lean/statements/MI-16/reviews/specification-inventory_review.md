# MI-16 independent pre-implementation specification review

**Verdict: APPROVE.** I am independent of the specification author. I compared the complete canonical target and the authored all-spectrum solution with `NUMERICAL_TARGETS.md`. This is an AI-agent statement review, not a proof audit of the manuscript and not approval of any future Lean boundary.

## Inputs and hashes

Published base: `0e916df335209819b5bf9bb8ed8f65ea978c049d`. SHA-256:

| Input | SHA-256 |
| --- | --- |
| `matrix-inequalities-and-norms/MI-16/README.md` | `81cabc2257bb13297711002f19a88ef6b156b28a2fa23140dd5c118deacb10fc` |
| `docs/lean/statements/MI-16/ORIGINAL.md` | `81cabc2257bb13297711002f19a88ef6b156b28a2fa23140dd5c118deacb10fc` |
| `docs/lean/statements/MI-16/NUMERICAL_TARGETS.md` | `41fa41fc723c67443cbf64f3b0a4aad6b5090449866d886d0f99234e5668ab01` |
| `matrix-inequalities-and-norms/MI-16/solution.tex` | `57fa815259b0fcfe658e3ed8502d4494cf0c2e8a993c60d647e976468c5232d1` |
| `matrix-inequalities-and-norms/MI-16/problem.tex` | `0cb0a4bcda0a0f1d182a76821c02b8f488428eb4be559f2bae0d4db9f618fb27` |

`ORIGINAL.md` is byte-for-byte identical to the canonical README (`cmp` succeeded).

## Exact-target comparison

The specification retains every positive order `n ≥ 1`, arbitrary ordered nonnegative real spectrum including zeros and repetitions, the complex **unitary** orbit `Uᴴ diag(λ) U`, and the full complex permanent sum. It requires an exact value from the eigenvalues, not an optimizer-existence assertion, an upper bound, or a restatement of the same optimization. It correctly includes attainment by some unitary and an upper bound for every unitary, with reality of the orbit permanent made explicit. There is no equal-diagonal-maximizer assumption, which would be false in general.

The finite critical-value construction matches Section 2 of `solution.tex`: the coefficient field is specialized `ℚ(λ₁,…,λₙ)`; `qλ` has one factor per **distinct** eigenvalue; the permanental adjoint deletes row `j`, column `i`; the ideal includes all first `n` power-trace equations, all entries of `qλ(A)`, all commutator entries, and `z−per(A)`; and the elimination polynomial is the monic square-free part of the monic generator of `Iλ ∩ F[z]`. The specification preserves the important distinction between real complex-critical roots and Hermitian-feasible objective values.

The explicit moment agrees with the source's finite character/Schur formula: positions `(a,i)` for `m=np`; row subgroup `H=(Sₙ)^p`; column subgroup `K=(Sₚ)^n`; character argument `kh`; factor `fν/m!`; partitions restricted to `length(ν)≤n`; and positive denominator `sν(1ⁿ)`. The finite sum, rather than an unevaluated Haar integral or a limit, is used in the selector. The Schur specialization handles repeated eigenvalues without dividing by eigenvalue gaps.

The selector matches the source's exact branches and numbers. Zero spectrum returns zero; a sole real candidate returns that candidate. Otherwise `B=L^n`, candidates are the distinct ordered real roots in `[0,B]`, `ρ` is the minimum adjacent gap, `b` is least with `2^b≥1+16n²B/ρ`, `h=ceil(4B/ρ)`, and `p=2n²bh`. The indicator is **strict** `T(n,p,λ)>rⱼ^p`. This gives the first candidate with `rⱼ^p≥T`, not the largest real root. The endpoints `n=1`, scalar and zero spectra, mixed zero/repeated spectra, and all-spectrum quantifier remain in scope. The source's `(1,3)` order-two check gives candidates `3,5`, first moment `13/3`, and answer `5`, as recorded.

The specification also correctly separates the general exact-value theorem from the optional one-exceptional-eigenvalue results, and makes no efficient general-evaluation claim. No mathematical or numerical mismatch requiring revision was found. Independent review of the eventual concrete Lean definitions, imported meaning, frozen boundary, and executable checks remains necessary.
