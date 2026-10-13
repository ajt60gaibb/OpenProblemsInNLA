# TR-14 one-factor local Fourier decomposition: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen source for aggregate import. It gives an exact local `N`-term symmetric multilinear expansion from a genuine Frobenius functional. It does not construct the global CRT bridge or prove a width.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/LocalFourierOneFactor.lean` | `3b0e9c148f6a01c6392c370c5949d4ab4ccd84552d1844cec7aa3ebef084f516` |
| Exact pre-implementation contract | `9bfa860893d7a7d049ea1c9ced1a508d2c10eed430680e95bd2dee3e9e51cc91` |
| Independent mathematical pre-review | `54fcc3fcd79b8788f9962729673e9933a2fb180b37bd8f3e6c92d36536e01a3e` |
| Separate imported audit `/private/tmp/tr14-onefactor-independent-audit.lean` | `d9a632f1b0580ea623629f64c8198af6c00a647326d8a69e4b9bf114d5b88b1e` |

The source takes the canonical monic polynomial remainder of every truncated class and proves its degree is at most `ℓ−1`. Each Fourier factor is a genuine complex-linear map `a↦eval_(ζ^j)(R_ℓ(w a))`; it never evaluates a quotient class at a nonzero root of unity. The product of `m` representatives has degree at most `m(ℓ−1)` and maps into the quotient as `w^m∏a_k=u∏a_k`. The quotient's top coefficient equals the unreduced polynomial coefficient at `ℓ−1`, which is `Λ(∏a_k)` by the reviewed Frobenius representation.

The proof expands the full finite polynomial evaluation through the exact degree bound and applies the audited inverse-character Fourier filter with `N=(m−1)(ℓ−1)+1`. The next aliased exponent is outside the bound, including `ℓ=1`. Polynomial evaluation of the product becomes a product of the same local linear factor in every mode. The public theorem preserves `m≥3`, `ℓ>0`, genuine nondegeneracy, exact `w^m=u`, a primitive `N`th root, and equality for **all** `Fin m` mode tuples.

The pinned Lean 4.33.1 direct module build passed 3,421 jobs. My separate imported LeanCert audit exited zero, checked the actual polynomial-remainder and linear-functional signatures and the exact public theorem, reran kernel assertions, and printed only `[propext, Classical.choice, Quot.sound]` for the main result. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

The local mode-vector coordinates, actual CRT decomposition of the global moment quotient, two symmetric width upper constructions, arbitrary ordinary lower bound, and full TR-14 Target remain open.
