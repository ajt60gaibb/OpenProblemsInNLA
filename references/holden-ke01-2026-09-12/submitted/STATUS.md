# Claim ledger

**General KE-01: not solved in this attempt.**

The following distinctions are part of the mathematical content, not merely implementation qualifications.

| Statement | Status | Where |
|---|---|---|
| Deterministic `O(N min(n, k+1+kappa log(2/epsilon)))` arithmetic solve | Proved for every input satisfying KE-01's promise | Theorem 2.1 |
| Target-form bound for `k=0`, `k<=kappa`, `N<=k^(omega_0-1)`, or `n<=2k` | Proved on each indicated regime | Corollary 2.2 |
| A one-outlier, constant-tail sparse matrix can have a dense Gram matrix | Explicit construction and proof | Proposition 3.1 |
| A unit-column row sketch at identity-tail regularization is automatically a constant spectral approximation | False in the stated generality | Proposition 3.2 |
| A one-pass rank-one Nyström construction always has constant additive spectral error | False in the stated generality | Proposition 3.3 |
| Input-sparsity solve for explicitly sparse SPD `M` with **exactly equal** tail eigenvalues | Proved using cited sparse OSE and fast algebra primitives | Theorem 4.1 |
| Unknown flat-tail value can be recovered with field operations and no exact eigenvalue oracle | Proved by characteristic polynomial and repeated gcds | Lemma 4.2 |
| PSD principal rank profile in fast-multiplication time | Divide-and-conquer proof supplied | Lemma 4.3 |
| Nonsymmetric exactly-flat singular-tail solve at cost `soft-O(sum_i w_i^2 + k^omega_0)` | Proved, including the physical-residual accuracy conversion | Corollary 5.1 |
| Replace `sum_i w_i^2` by `N` for every sparse input | Not established; that normal-equations accounting can be quadratic | Sections 3.1 and 5 |
| Replace an exactly flat tail by an arbitrary bounded-width tail in Theorem 4.1 | Not established; algebraic rank can jump to `n-1` | Section 6.1 |
| Construct a general sparse preconditioner satisfying the proposed sufficient guarantee | Not established | Proposition 6.1 is conditional |
| Prove no algorithm can achieve KE-01 | Not established; no such lower bound is claimed | Sections 3 and 6 |
| Implement the theoretical fast-multiplication/OSE solver in production-quality code | Not done | Code is an exact small-instance reference/verifier |
| Finite rational checks of all listed identities and examples | Passed | `results/` |
| Formal proof-assistant certification of the report | Not done | Human-readable mathematical proofs are supplied |

## The precise sufficient primitive that is missing

For `H=A^T A`, one sufficient route would construct a fixed SPD `P` satisfying

\[
H\preceq P\preceq C\kappa^2 H
\]

in `soft-O(N+k^omega_0)` operations and apply its exact inverse in `soft-O(N)` operations, with appropriately bounded failure and worst-case work. Preconditioned CG and the energy/residual identity would then give the requested target. This is a sufficient route, not a necessary characterization.

A dense `k`-dimensional core whose inverse application costs `k^2` cannot automatically be charged as free: repeating it `O(kappa)` times yields `k^2*kappa`, which is not uniformly absorbed by the target. The flat-tail theorem only needs a logarithmic number of its inner core iterations, which is why its accounting works.

## Why the exact-flat proof stops

For exactly flat SPD input, `M-alpha I` is a sparse PSD matrix of algebraic rank at most `k`. A sparse sketch therefore gives an exact sparse low-rank representation. Under only a tail-ratio bound, that difference can have rank `n-1`, even when the ratio is arbitrarily close to one. For general nonsymmetric input, explicitly forming the normal matrix can also destroy the input-sparsity budget. Neither step has been repaired in this attempt.

The positive restricted results have not been independently peer-reviewed, and no novelty or priority claim is made.
