# RA-10 independent specification review

Reviewer: OpenAI Codex agent `/root/inventory` (AI), independent of specification author `/root/statement_design`.

Phase: `specification`. Verdict: **APPROVED** for the exact mathematical target, subject to the explicit formal implementation obligations recorded below. No target implementation existed when reviewed.

Read the full canonical README and full specification; verified the complete ORIGINAL snapshot byte for byte and checked every retained source-lock hash.

The single real constant C>=1 precedes every n,k,A,Ahat,epsilon,f and both ordered eigenbasis choices. The matrix domain is every real PSD pair with n>=2 and 1<=k<n, and epsilon>=0. No ordering, commutation, invertibility, gap, or simple-spectrum premise is added.

The operator-monotone hypothesis quantifies over every matrix size and the genuine PSD order. Scalar concavity/monotonicity alone is explicitly insufficient. The function is continuous and nonnegative on [0,infinity); extending its domain to all reals while leaving negative inputs unused does not impose additional continuity outside the original domain.

The independent eigenbasis choices for A and Ahat are universally quantified. Each matrix uses its same selected basis for its ordinary and functional truncations. This retains every tie and selected zero direction, including rank below k and f(0)>0; replacing f(Ahat)_k by f(Ahat_k) would be wrong and is excluded.

The nuclear norm is the actual sum of singular values. All displayed constants, the weak error premise and conclusion, and the zero-tail/epsilon-zero cases agree with the source. The stronger resolution constant 11 is kept separate from the original existential target.

The source models are mathematically complete enough for statement implementation. Actual spectral calculus, norm and all-size order definitions must be inspected in the later Lean-boundary review; no numerical approximation is necessary.

This approves mathematical specification correspondence only. It does not certify a Lean implementation, the correctness of cited resolution proofs or supplemental reduction lemmas, compilation, a numerical proof, or a Linux Comparator run. The source-lock hashes were checked, but hashing a cited proof is not an independent proof audit.

## Reviewed input hashes

- `randomized-and-low-rank-approximation/RA-10/README.md`: `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742`
- `docs/lean/statements/RA-10/NUMERICAL_TARGETS.md`: `9a736152257f91d97f113a7b8b43d286e268a25fa142a97bdd62214387cb85de`
- `docs/lean/statements/RA-10/ORIGINAL.md`: `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742`
- `docs/lean/statements/RA-10/source-lock.json`: `ab767b22f532c6a3fef7776bcca49e6a7bc752914ed16db19afb9fc1506c91d8`
