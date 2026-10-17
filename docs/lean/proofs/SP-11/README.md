# SP-11 proof development

**Incomplete.** No theorem of the frozen `NLA.Statements.SP11.Target` has been
proved. The canonical Solved status, original text, permanent ID and source
credits are unchanged. The substantive delta theorem is H. Tracy Hall's
[*The Delta Theorem*](https://arxiv.org/html/2601.01211v1); this development
formalizes its representation route with OpenAI Codex AI agents.

The exact all-graph boundary is the published, independently reviewed
`lean-statements/NLA/Statements/SP11.lean` and its frozen `Reviewed/SP11.lean`.
The two dated statement reviews in this directory recheck that boundary.
The new modules under `lean-statements/NLA/Proofs/SP11/` prove:

| Module | Actual result |
| --- | --- |
| `GreedyOrdering` | A complete greedy vertex listing exists; its earlier-nonneighbor counts obey the required inequalities. The final count determines an ambient dimension at most `n − δ(G)`. |
| `AlternatingContraction` | Contraction of an actual alternating form is exactly orthogonal to every input, over any commutative ring. |
| `AlternatingPolynomial` | Concrete polynomial alternating forms are finite sums of determinant minors with named coefficient variables. |
| `UniformLSS` | The finite, well-founded vertex recursion exists and every distinct nonedge has exactly zero inner product. |
| `PolynomialLSS` | The actual polynomial recursion has one shared coefficient family per vertex. Its nonedge Gram polynomials vanish identically. |
| `PolynomialFaithfulness` | Finitely many nonzero real polynomials can be made nonzero at one actual parameter point, yielding faithfulness when the edge/diagonal polynomials are nonzero. |
| `GramBridge` | A faithful real representation of dimension at most `n − δ(G)` yields the exact symmetric matrix and nullity required by SP-11. |

The central missing theorem is Hall's non-cancellation result for the **actual
shared-variable** polynomial recursion in a greedy order. Edge and diagonal
Gram polynomials must be proved nonzero, with repeated vertex variables
preserved. Relabeling the greedy listing into the fixed-order recursion and
final unconditional assembly also remain. None of these obligations is an
axiom or a field silently supplying the conclusion: every conditional lemma
retains its hypotheses in its exported type.

The support lemmas use exact algebra, finite combinatorics, and LeanCert
`#assert_trust kernel`. They require no numerical interval certificate.
Independent source reviews and fresh local-build evidence are retained here
and in [campaign verification](../../campaign-2026-10-17/verification/).
The existing `lean-statements` CI aggregate imports all seven modules.
The shared Comparator job verifies frozen statement identities; it does not
verify these conditional support lemmas as a complete SP-11 proof. A final
self-contained Challenge/Solution project and successful fresh Linux
Comparator/kernel run are still required for the full target.
