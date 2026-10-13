# MF-03 finite elementary coefficient limit: independent final review

**Independent mathematical/source reviewer:** `/root/sp14_base_proof`, 10 October 2026. **Imported signature/kernel auditor:** `/root`. **Verdict:** APPROVE the frozen finite coefficient definition and four exact theorems for aggregate import. The determinant/tableau bridge and full target remain open.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/MF03/FiniteElementaryLimit.lean` | `d8d28308b89e7dc6144b4b0aba7897008cac31630ce865a5eea2b3647b625989` |
| Exact mathematical precontract `FINITE_ELEMENTARY_LIMIT_PRE_REVIEW.md` | `553c301c927251159859441f3978870c0a4ab1ce3f8bb75fe812746a7ee7df15` |
| Independent pre-review `FINITE_ELEMENTARY_LIMIT_INDEPENDENT_PRE_REVIEW.md` | `354e609fbddfe3b0f1aeeb1a1b80e7e32861b3d690ce6d220d23a56e0032c53c` |
| Separate imported audit `/private/tmp/mf03-finite-elementary-limit-independent-audit.lean` | `43b08e841c54ecc1ee2f81a44ca72b223d20e117be89355ca0b40de01a2b37c2` |

The finite coefficient is exactly the sum of product weights over `powersetCard j (Finset.range N)`, with the original zero-based factor `cosineFactor(k+1)`. The independent reviewer checked its exact identification with the existing infinite cardinality-subtype coefficient: select cardinality `j` inside all finite subsets, prove full-product summability, and use the `tsum_subtype` identity. The cutoff powersets of `Finset.range N` are nested and exhaust every finite subset, so the finite sums are nonnegative, monotone in `N`, bounded by `cosineElementaryCoeff j`, and converge to it for every `j`. The general proofs include `N=0`, `j=0`, and `j>N` without altering any coefficient.

The pinned Lean 4.33.1 module build passed 8,714 jobs. A separate imported audit reconstructed the exact finite definition and all four public signatures, reran LeanCert `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]`. A source scan found no proof escape. This coefficient limit alone does not prove a determinant limit, dual Jacobi–Trudi identity, all-order Padé pair, or the frozen MF-03 Target. Changed source bytes require a new review.
