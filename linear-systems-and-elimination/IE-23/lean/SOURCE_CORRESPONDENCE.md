# IE-23 source and Lean statement correspondence

Canonical upstream commit:
`f41f1f9ffa2171550d4bb795862c6170c4f26070`.
The original ID and path `linear-systems-and-elimination/IE-23/README.md` and
its mathematical target are retained. The canonical status is Solved; this
statement-only candidate does not change it.

The complete canonical README, complete standalone Colbrook manuscript
`references/colbrook-recovered-2026-09-11/manuscripts/IE-23.tex`, and complete
independent informal review were read before drafting. The source's historical
provisional-status prose is explicitly superseded by its later independent
review and the canonical resolution record; no stale qualifier is used to
alter the formal target.

| Original object or claim | Concrete Lean representation / proof obligation |
| --- | --- |
| Complex rectangular matrices, all `1≤m<n` | `Mat m n`, with independent natural dimensions in the complete conjecture |
| Rank(A)=m | `FullRowRank A := A.rank=m`, Mathlib's actual complex range dimension |
| `A†=A*(AA*)⁻¹` | `moorePenrose`, using actual conjugate transpose and actual totalized matrix inverse; the witness's invertibility is proved |
| Induced direct `p→2` norm | `ratioSet` and `inducedNorm`, exact nonzero-input supremum with the true Euclidean numerator and finite-real-p denominator |
| `2<p<∞` | Real p with `2<p`; a real parameter is always finite, and p=2 is excluded |
| Every distinct right inverse | `IsRightInverse A X` and the full universal `RightInverseUniqueConjecture`, with no real-only or family restriction |
| Colbrook Theorem 1, unchanged rational A,B,X | `witnessA`, `witnessB`, `witnessX` and `witness_matrix_identities` |
| Theorem 1 specialized to p=4 | `fourth_power_norm_control`, `witness_attainment`, and the actual supremum equalities `witness_norms` |
| Source Section 1 / global optimality | Exact special-matrix action identity for every complex right inverse, then `witness_global_minimizers` including an actual `IsLeast` |
| Negative answer to original conjecture | `not_rightInverseUniqueConjecture`, not merely a pair of finite matrix products |

The source's all-p proof invokes the standard finite-dimensional norm comparison.
The formal route specializes the counterexample to p=4 and proves the required
comparison directly from `(a²−b²)²≥0`. This avoids general Hölder/Schatten or
spectral comparison developments while preserving the entire original
conjecture as the final negated proposition. It changes no displayed matrix
or norm objective. The competitor identity uses complex t, so all complex
right inverses remain covered.

Primary attribution was independently checked against the
[Dokmanić–Gribonval author PDF](https://dokmanic.ece.illinois.edu/assets/pdf/DokmanicG17aa.pdf),
arXiv:1706.08349v2, Example 4.1, equations (51)–(53), pp.16–17. It contains the
same A and Moore–Penrose inverse. Corollary 4.2(3) and Remark 4.1 on p.18
distinguish the direct and product uniqueness questions. This formalization
does not claim the source example as new. The actual primary page/extract
locators and source hashes are retained with the statement evidence.

No separate noncommutative CFC or matrix singular-value bridge is needed for
this target: the canonical pseudoinverse is already given by the actual
inverse formula, and the induced norm is already given by an explicit
supremum. Their nonvacuity and exact semantics still require generic
denominator/boundedness/LUB conclusions plus actual witness invertibility.

The library configuration and fresh-build method reuse the campaign's MI-22,
MI-03, and IE-19 project structure, with the same exact Lean 4.33.1, Mathlib,
and LeanCert pins. No mathematical proof has been imported or implemented at
the statement stage. Mathematical authorship remains Colbrook's; formalization
credit is George Stepaniants with the approved Caltech department affiliation,
without a new contact email.
