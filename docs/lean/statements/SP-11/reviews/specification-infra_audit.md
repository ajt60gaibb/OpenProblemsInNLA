# SP-11 independent preimplementation specification review

Reviewer: `/root/infra_audit`, an OpenAI Codex AI agent independent of the target specification author. Phase: specification. Verdict: **approve**.

I read the complete canonical README and exact specification and independently checked the mathematical representation before target Lean implementation. Infrastructure authorship does not make this reviewer an author of these problem specifications.

The source already gives the existential matrix formulation directly. Quantifying over every SimpleGraph on Fin n with n >= 1 covers every finite simple undirected graph up to vertex relabelling and retains isolated vertices and singleton graphs.

Real symmetry and the off-diagonal equivalence Aij != 0 iff adjacency specify exactly S(G). No diagonal condition, edge sign, PSD, SAP, connectedness or girth restriction was added.

For real square n-by-n matrices, rank is at most n and rank-nullity identifies natural subtraction n-rank(A) with the real dimension of the kernel. Thus the proposed weak nullity comparison is the original inequality, provided the actual Lean API denotes this ordinary matrix rank.

The minimum vertex degree is the minimum ordinary neighbor cardinality over the nonempty vertex type. This imported API and the rank API must be inspected again in the Lean boundary review. The complete canonical README is retained byte for byte.

This approval is specific to the following bytes and establishes specification fidelity only. It does not certify the cited resolution, a Lean proof, human peer review, or Linux Comparator execution. The implemented boundary still requires independent review.

- `eigenvalues-and-inverse-problems/SP-11/README.md`: `8e3edc4c7c6c8b388ab7bbf87bc197b76756210b19338d27398af356016aa865`
- `docs/lean/statements/SP-11/NUMERICAL_TARGETS.md`: `a0cd200e8bd4dca2a9b0c7a690e874d67b1d4df9f7179ab9db738c4a8ee88b00`
- `docs/lean/statements/SP-11/ORIGINAL.md`: `8e3edc4c7c6c8b388ab7bbf87bc197b76756210b19338d27398af356016aa865`
