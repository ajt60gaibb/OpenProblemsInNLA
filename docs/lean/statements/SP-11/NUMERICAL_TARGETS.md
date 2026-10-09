# SP-11: exact statement specification

Author: OpenAI Codex agent `/root` (AI). Phase: preimplementation specification. No Lean target or proof has been implemented.

Canonical source: `eigenvalues-and-inverse-problems/SP-11/README.md` at `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`, SHA-256 `8e3edc4c7c6c8b388ab7bbf87bc197b76756210b19338d27398af356016aa865`. [ORIGINAL.md](ORIGINAL.md) preserves the entire source byte for byte, including the complete problem, history and attribution.

## Exact target and conventions

For every natural n >= 1 and every finite simple undirected graph G on Fin n, there exists a real n-by-n matrix A which is symmetric and satisfies, for distinct i,j, A i j != 0 if and only if G.Adj i j, and whose kernel has real dimension at least the minimum vertex degree of G. No diagonal restriction, edge-weight restriction, PSD condition, SAP condition, connectedness, girth, or regularity is imposed. Isolated vertices and the n=1 graph are included.

The planned nullity expression is n - Matrix.rank A; subtraction is natural subtraction and rank A <= n for every real n-by-n matrix, so rank-nullity makes this exactly dim ker A. The graph minDegree API must be checked as the minimum of ordinary neighbor cardinalities on a nonempty vertex type. The nonzero pattern is an equivalence at all off-diagonal entries, not only one implication. The whole target is existential A for each G. No optimum or topology is needed because the question explicitly gives this equivalent witness formulation.

Numerical data: n >= 1, all real exact values, weak nullity bound. Edge entries can have either sign. No numerical certificates are required.

## Planned Lean boundary and review

The declaration `NLA.Statements.SP11.Target : Prop` will define the question. It will not assert a proof. There will be no target axiom, `sorry`, arbitrary supplied invariant, or unimplemented semantic field. Two independent preimplementation specification approvals are required, followed by two independent reviews of the actual Lean definitions and imported meanings, bound by source hashes.

## Computation and scope

The statement itself requires no interval computation. Exact finite algebra suffices; no domain is reduced. Any future numerical proof uses explicit LeanCert kernel trust. The shared kernel smoke test establishes no catalog target. The existing Solved status and mathematical credits remain as in ORIGINAL.md. This draft claims no mathematical proof, human peer review, or Linux Comparator verification.
