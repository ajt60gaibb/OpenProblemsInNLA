# RA-03 independent statement review request

Stage 1 is complete. `lake build NLA.RA03.Definitions Challenge` passed with 2723 jobs and exactly the four intentional Challenge placeholder warnings. There is no proof implementation or `Solution.lean` yet.

Read the complete canonical RA-03 README and Colbrook manuscript at base `e7252e5307781a7c897bca6cb124f6ab838f6809`, then the three frozen boundary files:

| File | SHA-256 |
| --- | --- |
| `NLA/RA03/Definitions.lean` | `de6509ef6b4a41db3e01fce7b77af4c7c338dbd61f8f135e956602d3b8b0980f` |
| `Challenge.lean` | `74a7c727e8cf2fa1ee26e78cfab812626b265abe8211e09f144a3c78fca5345e` |
| `NUMERICAL_TARGETS.md` | `91618c7848ad46931a8f59bad6ff2900bf53b1e1dde22f31383c4a3941eb4a94` |

Full source, configuration, and numerical-precheck hashes are recorded in `statement-freeze.json`. The mathematical checks requested are:

- Joint entry-pivot distribution with no row/column or temporal independence assumption; exact full cross update; zero-probability updates and zero-residual absorption.
- Finite history mass and expectation semantics for arbitrary dimensions and all step counts; public general normalization and nonnegativity obligations are sufficient to certify a genuine probability law.
- Actual mathlib Euclidean singular values in decreasing order, complex matrices, and correct zero-based tail cutoff at `min(m,n)`.
- Original quantifiers, all admissibility conditions, factor `2^k`, and squared Frobenius error are preserved.
- Four exact witness updates and probabilities, true spectral values, full finite expectation, and strict violation imply the complete original universal negation.
- No expected-error lookup, spectral list, algorithmic property, or comparison has become an unproved assumption; no restricted special-case statement replaces the target.
- Colbrook retains mathematical attribution; George Stepaniants and his Caltech department are credited only for the formalization.

Please record independent scoped verdicts with the three source hashes before implementation. Changes to this boundary require re-review. Final proof review and Linux Comparator are later gates and are not claimed at this stage.
