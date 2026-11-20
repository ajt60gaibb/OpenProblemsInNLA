# Independent proof-contribution review — referee 2

Date: 24 September 2026. Reviewer: Codex AI agent `/root/tr06_statement_referee_2`. Scope: the Generic, Radial, PolynomialNull, and LinearNorm proof contributions authored by other agents. Verdict: **approve these contributions for integration at the hashes below**. This is not approval of the full TR-06 formalization.

I inspected the actual source and then independently compiled snapshots in this directory using pinned Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. Every module exited zero, with no warnings or placeholders. All seven exported statements report only `propext`, `Classical.choice`, and `Quot.sound`, and their LeanCert `#assert_trust kernel` commands pass. Source snapshots, command logs, and hashes are retained under `NLA/TR06/` and `evidence/receipt.json`.

| Module | SHA-256 |
|---|---|
| `Generic.lean` | `692c0409eae986845fbab4b033c130c6784fddb5a41f7aae120874e2fb4261b9` |
| `Radial.lean` | `7d3a60f22f8e0ea6f7e51a0968503b2271a1578115d8d9fedb9d4ebb90c288ef` |
| `PolynomialNull.lean` | `7dd68dd61f60bafea549cee25cb39bcd3595f70f327f01d8fc13801d406dc56f` |
| `LinearNorm.lean` | `9d876d5d9c96fbbe2ca224a90f976a65a6274bd876cb1d005fd22cc79bebde48` |

`generic_iff_source` matches the frozen Challenge exactly. The forward proof uses the singleton polynomial family; the reverse proof selects the polynomial already violated by the properness witness. The genericity conclusion is then applied only at actual exact-rank-r tensors. There is no added geometric or integrability premise.

`derivativeRatio_eq_operatorNorm` also matches the frozen Challenge exactly. The injective input differential is inverted onto its range, whose norm is the induced tensor Frobenius norm. The upper bound makes the ENNReal ratio supremum finite before conversion to a real number. The lower bound applies the ordinary operator norm inequality to every vector in that range, with the zero vector handled separately. Thus neither division by zero nor `toReal` of infinity can hide a missing case. Zero-dimensional domains are included correctly.

`expectedDimension_gt_one` is a valid stronger elementary bound: r >= 3 alone implies the threshold because the factor `1 + sum(n_j - 1)` is positive even without the admitted format conditions. `radial_integrable` uses the exact exponents k-2 and k-1 on `(0, infinity)`, the exact Gaussian coefficient 1/2, and the existing general Gaussian integrability theorem. It makes no claim about the angular link integral or the complete expectation. There is no unnecessary numerical computation.

`real_polynomial_zero_locus_null` correctly handles a nonzero complex polynomial evaluated on real coordinates. It proves the zero-dimensional case directly. Its induction chooses a nonzero polynomial coefficient in the last coordinate, excludes the lower-dimensional coefficient-zero locus by the induction hypothesis, obtains a nonzero one-variable complex polynomial on each remaining fiber, and uses finiteness of its real roots plus Fubini. The coordinate split is explicitly measure preserving. Continuity proves measurability before the product-null theorem is applied. The result is ambient coordinate-space Lebesgue nullity; it must not later be misused as induced lower-dimensional tensor-variety nullity without an additional bridge.

The proof files preserve George Stepaniants's name and Caltech affiliation and Colbrook's original proof attribution. No custom axioms, Challenge imports, native computation, or weakened target signatures were found. The use of `Mathlib.Tactic` is broad but does not affect transitive trust or mathematical scope.

Limitations: these were local macOS development checks using existing package artifacts, not authoritative Linux sandboxed Comparator runs. I did not author these four implementation modules, but I did participate in prior statement design/review. Full-problem promotion still requires complete-target proofs, all reviewed correspondence statements, reproducible Linux checking, permitted-axiom audits, and independent final review of the integrated implementation. My separate MetricSlope contribution is not independently reviewed by this report.
