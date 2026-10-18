# SP-12: exact statement specification

Author: OpenAI Codex agent `/root` (AI). Phase: preimplementation specification. No Lean target or proof has been implemented.

Canonical source: `eigenvalues-and-inverse-problems/SP-12/README.md` at `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`, SHA-256 `cdc8003bc5160604408ce6b95c344a4ea1b9bfbf8af0f99ae1e8e016648d53e1`. [ORIGINAL.md](ORIGINAL.md) preserves the entire source byte for byte, including the complete problem, history and attribution.

## Exact target and conventions

For every natural n >= 1 and every simple undirected graph G on Fin n, there exists a real n-by-n matrix A with: symmetry; off-diagonal A i j != 0 if and only if G.Adj i j; positive semidefiniteness; the strong Arnold property; and real nullity at least chi(G)-1.

PSD means x^T A x >= 0 for every real vector x (equivalently Mathlib real Matrix.PosSemidef, with symmetry). SAP quantifies over every real symmetric n-by-n X and says that if A*X=0, for every i,j A i j * X i j = 0, and for every i X i i=0, then X=0. A*X is ordinary matrix multiplication; the second condition is the entrywise product. The I Hadamard X condition is exactly zero diagonal; it is not replaced by a matrix product. Diagonal entries of A are unrestricted apart from PSD and SAP.

Define chi(G) concretely as the least natural c admitting a function f:Fin n -> Fin c with f i != f j whenever G.Adj i j. A coloring always exists with c=n. Since n>=1, chi>=1, and natural subtraction chi-1 equals the intended integer difference. A least-natural definition can use sInf of this nonempty set; it is not a freely supplied invariant. Nullity may be n - Matrix.rank A using the real rank-nullity theorem. The witness formulation is exactly equivalent to the displayed maximum-nu inequality because feasible nullities form a nonempty finite subset of {0,...,n}; the source's relevance paragraph expressly uses this formulation.

Disconnected graphs, isolated vertices, n=1, and rank-zero cases are retained. No vertex-critical restriction is imposed. No required numerical bound, probability, or algorithm is added.

## Planned Lean boundary and review

The declaration `NLA.Statements.SP12.Target : Prop` will define the question. It will not assert a proof. There will be no target axiom, `sorry`, arbitrary supplied invariant, or unimplemented semantic field. Two independent preimplementation specification approvals are required, followed by two independent reviews of the actual Lean definitions and imported meanings, bound by source hashes.

## Computation and scope

The statement itself requires no interval computation. Exact finite algebra suffices; no domain is reduced. Any future numerical proof uses explicit LeanCert kernel trust. The shared kernel smoke test establishes no catalog target. The existing Solved status and mathematical credits remain as in ORIGINAL.md. This draft claims no mathematical proof, human peer review, or Linux Comparator verification.
