# PF-05: exact statement specification

Author: OpenAI Codex agent `/root` (AI). Preimplementation specification; no Lean target has been implemented.

Canonical source: `nonnegative-and-positive-factorizations/PF-05/README.md` at `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`. SHA-256: `f7acc0629067696f7aa2828673740e286730fb9654348b742752eb146a840f71`. The complete source is preserved byte for byte in [ORIGINAL.md](ORIGINAL.md), including original target, attribution and history.

## Exact mathematical target and numerical conventions

Quantify over every pair of natural dimensions p,q, every entrywise nonnegative real p-by-q matrix M of ordinary real rank three and PSD rank two, and every fixed real size-two PSD factorization (A_i,B_j) with M_ij=trace(A_i B_j). Ordinary rank three automatically excludes zero dimensions. A size-k PSD factorization consists of symmetric positive-semidefinite real k-by-k matrices indexed by rows and columns with exactly these trace equations. PSD rank two can be stated concretely as existence of a size-two factorization and nonexistence of a size-one factorization, since the original minimum is over integers k>=1.

For the fixed size-two factors, quantify over all families of real symmetric 2-by-2 matrices E_i,F_j. Feasibility means both: for every row and column, trace(E_i B_j)+trace(A_i F_j)=0; and there exists one real h>0 such that for every real t with 0<=t<h all A_i+t E_i and all B_j+t F_j are PSD. The same h applies to all factors. The second condition is the actual straight-line segment condition, not an arbitrary tangent-cone test. Exact factorization of M at t>0 is NOT required.

Rigidity means every such feasible direction has E_i=d A_i and F_j=-d B_j for one real scalar d shared by all row and column factors. Uniqueness means every other real size-two PSD factorization tilde A,tilde B of M is related to the fixed factors by one real invertible 2-by-2 matrix S: tilde A_i=S^T A_i S and tilde B_j=S^{-1} B_j (S^{-1})^T. The target is the equivalence between rigidity and uniqueness for every fixed factorization in the stated domain. Inverse notation must only occur with det S!=0 (or an equivalent invertibility assertion).

Numerical and domain conventions: size exactly two; ordinary rank exactly three; PSD rank exactly two; real scalars and bilinear transpose; trace constraint only first order; segment [0,h) includes zero and excludes h; h strictly positive; exact equalities; no normalization or positive-definite assumption. Zero entries of M, repeated or singular factors, and zero rows/columns are included. No objective, probability, runtime or numerical certificate is required. All helper predicates must expand to concrete finite matrices, multiplication, traces, and quadratic-form/PSD definitions.

## Review, implementation and scope

The future `NLA.Statements.PF05.Target : Prop` will define the full proposition, without asserting a theorem proving it. Two independent specification approvals must precede implementation. Final independent boundary reviews must inspect all actual definitions and their imported meanings. No target axiom, unimplemented predicate, free semantics or `sorry` is permitted in the proposition.

The existing Solved status and mathematical authorship remain those of the canonical source. This draft claims neither a new proof nor formal verification of the solution. No artificial computation is needed for statement elaboration. The shared LeanCert kernel smoke test is not a proof of this problem.
