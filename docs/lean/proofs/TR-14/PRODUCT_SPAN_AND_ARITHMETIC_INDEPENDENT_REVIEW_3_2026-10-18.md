# TR-14 actual quotient-mode product span and block arithmetic — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I authored neither module. **APPROVE these exact support sources.** They do not construct ordinary decomposition blocks or prove the full ordinary lower bound/Target.

| Module | SHA-256 |
| --- | --- |
| `QuotientProductSpan` | `6c65f76dcdf65880f7edcd5596049dc5c6dc1af8cf573f59237156dcbd6be355` |
| `NumericalBlockLower` | `a6cc22b3248cb4f65f2c1bef58d4ad2566b384c1a80b79c6df6f6dca1ab332b9` |

`QuotientProductSpan` bundles the actual quotient-mode sum as a complex linear map. Each root power through q is the image of its actual coordinate basis vector. Induction on the number c of factors splits any exponent j≤c*q using its minimum with q; the residual exponent is bounded by the remaining factors and their sum is exactly j. Thus membership is proved in the real Mathlib span-of-products submodule power, not a supplied product-span predicate. The zero-factor case uses the actual scalar subspace and exponent zero. Once degree(g)≤c*q+1, all monic quotient power-basis vectors lie in that product, so their spanning property proves equality to the whole quotient. The rank-minus-one variant states its positive-degree assumption explicitly. c=0, q=0, linear modulus and the degree-zero monic/unit modulus case retain their literal meanings; no nontrivial-quotient or positive-q hypothesis is silently added.

`NumericalBlockLower` is a finite arithmetic consequence of its explicit data. If some block dimension reaches n, that block's stated inequality, its two bounds by the partition totals and r≤D give `D-r+2≤R`. Otherwise every minimum is the block dimension; rewriting m=(m−1)+1 and summing yields `(m−1)r≤R+(m−2)t`. The explicit t≤s then yields the local bound `(m−1)r−(m−2)s≤R`, so either branch bounds the minimum of the two displayed upper widths. The natural subtraction in the binary branch is guarded by r≤D, and the local branch uses the exact natural subtraction inequality. m≥3 and n≥2 are retained. Empty/zero block arrays are not incorrectly excluded.

The arrays' dimension totals, t≤s and each block inequality are actual premises. This module neither supplies them for a tensor nor assumes an equivalent full lower-bound oracle. Later proof code must construct the blocks, prove those identities and inequalities, and use the same r/s as the selected chart. This review does not mark that application complete.

Independent fresh immutable verification passed **15 Lean commands**: 14 actual local sources plus a separate consumer. It audits **94 explicit declarations**, including **63 theorem/lemma constants**. Private constants in imported chart foundations are resolved uniquely by actual environment name; theorem constants require theorem kind and private definitions/abbreviations require definition kind. Every constant passes LeanCert kernel trust and transitive printed axioms; only propext, Classical.choice, Quot.sound occur. All source bytes and all ten pinned dependency trees pass before/after. Local objects are rebuilt in a fresh private output prefix excluding campaign project objects; pinned cached dependency objects are reused.

Reproduce from the repository root:

```bash
python3 docs/lean/proofs/TR-14/verification/check-product-span-and-arithmetic.py \
  --top QuotientProductSpan NumericalBlockLower \
  --evidence-name product-span-and-arithmetic-review-3
```

Exact driver, source/consumer snapshots, hashes and logs are in [verification/product-span-and-arithmetic-review-3/](verification/product-span-and-arithmetic-review-3/). Imported mathematical foundations retain their separate reviews; this independently reviews the two newly frozen gates and gives fresh kernel evidence for their exact closure. No proof, statement, permanent ID or original canonical page was edited. This is local macOS Lean4.33.1 evidence, not full Target proof, Linux Comparator acceptance, source-author endorsement or external human peer review.
