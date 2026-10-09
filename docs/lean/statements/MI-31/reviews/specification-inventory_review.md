# MI-31 independent pre-implementation specification review

**Verdict: APPROVE.** I independently compared the specification with the entire canonical MI-31 page. This is an AI-agent review of the mathematical and numerical statement before Lean implementation, not a proof audit of the cited candidate preprint or approval of future Lean definitions.

## Reviewed inputs

Published base: `0e916df335209819b5bf9bb8ed8f65ea978c049d`. SHA-256:

| Input | SHA-256 |
| --- | --- |
| `matrix-inequalities-and-norms/MI-31/README.md` | `9d49717605baf2379896f6360417092c70bb74773120002cd5f4c15950a04093` |
| `docs/lean/statements/MI-31/ORIGINAL.md` | `9d49717605baf2379896f6360417092c70bb74773120002cd5f4c15950a04093` |
| `docs/lean/statements/MI-31/NUMERICAL_TARGETS.md` | `e1d5dc6fdb06b16cbcf95d2a648f435d4cdd8bcefd2a0e13034e0cfe93556b76` |

`ORIGINAL.md` is byte-for-byte identical to the canonical README.

## Exact-target comparison

The specification covers every positive rectangular dimension pair, all real variance profiles `A`, every `1≤p≤2`, and the full extended range `2≤q≤∞`. It retains independent **standard real** Gaussians for every matrix entry and the entrywise product `G_A(i,j)=A(i,j)g(i,j)`. A single positive constant is chosen before all dimensions, exponents, and matrices; allowing it to depend on `p` or `q` would change the original conjecture.

The `p→q` norm is the actual induced operator norm over the entire real `ℓ_p` unit ball. The conjugate exponent uses `p*=∞` at `p=1`; both that endpoint and `q=∞` use the ordinary coordinate maximum norm. `L(k)=max(1,ln k)` uses the natural logarithm, including `L(1)=1`, and the conventions `min(∞,L(k))=L(k)` preserve finite square-root factors at both infinity endpoints.

The deterministic first term is the maximum **row** `ℓ_{p*}` norm, with the `n`-dimension logarithmic cap. The second is the maximum **column** `ℓ_q` norm, with the `m`-dimension cap. The third term is the expected maximum of **all** absolute Gaussian entries after variance scaling; its maximum is inside the expectation. The left side is the expectation of the genuine induced operator norm. All three terms and their plus signs match the canonical formula, including `m=1`, `n=1`, `p=1`, `p=2`, `q=2`, and `q=∞`.

The target is an **upper bound only**. The specification correctly excludes a spurious matching lower-bound assertion and retains the canonical warning that the cited candidate proof's entropy-cover convention required correction. No mathematical or numerical mismatch was found. The later Lean boundary must concretely define the Gaussian product law, norms, maxima, and expectations; uninterpreted stand-ins would reopen this review.
