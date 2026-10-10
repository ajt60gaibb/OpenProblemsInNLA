# TR-14 root factorization, CRT and local Frobenius transfer: independent pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen exact contract for staged implementation. It specifies an algebra CRT and every local moment through the full Hankel degree, without a global width or full Target claim.

| Reviewed input | SHA-256 |
| --- | --- |
| `LOCAL_CRT_TRANSFER_PRE_REVIEW.md` | `d267bd05e2f9ce15bc5c76c6614e6ce66f627b6e1f6a1c235eebcb06ddbcf184` |
| Frozen `NLA.Statements.TR14` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Audited quotient and Frobenius sources | `3c6809e84eb522ad82c28f49245b80ef6da7da84cd201f46f4cbfb54a363a54d`; `dca235b899ba5729e5bdfb50986e55836989c2736b133ee6e2b4a7f428dee29e` |
| Audited local mode source | `ab77987b8b5448ef24f59ca6c49a2598011f3b13babda48ca9cb09febe2c6626` |

For monic `g` of positive degree `r`, its complex root multiset counts all multiplicities. On its support `S`, each `ℓ_α` is positive, `g=∏(X−α)^ℓα`, and `Σℓα=r`. Distinct supported roots yield pairwise coprime factors. Ideal CRT therefore gives a **complex-algebra** equivalence from `AdjoinRoot g` to the product of local quotients; the translation in the `α` factor must send the global root to `α+z_α`. No equality of support cardinality with `r` is assumed, and `ℓα>n` is allowed.

The local functional is the global `Λ` transported through the inverse equivalence after insertion into just one product component. Supported insertion is linear and generally nonunital; the contract uses only its correct componentwise multiplication identity. Decomposing every tuple into supported components gives `Λ(x)=Σ_αΛ_α((E x)_α)`. If a local class pairs to zero with all local classes, its supported global preimage pairs to zero with every global class; genuine global Frobenius nondegeneracy then forces it to vanish. This proves, rather than assumes, each local Frobenius property.

The audited normalized quotient matches **every** supplied moment through `D`, not just the first `r`; combining that with the root image and functional sum gives the exact formula for every `j≤D`. With `D=m(n−1)`, each zero-based Hankel index is within that range, yielding the stated coordinate identity. The contract keeps the original projective-root multiplicity correspondence open beyond the existing invertible chart theorem; no numerical node-count formula in original coordinates is silently claimed. Cases `r=1`, repeated roots, mixed multiplicities, balanced kernels, zero moments and roots initially at infinity have the stated scope.

Implement in separately frozen root, algebra CRT, functional and moment gates as needed. Each must preserve multiplicity, scalar compatibility and the complete all-moment range, and remain unimported until an independent source/signature/LeanCert kernel audit. The global symmetric upper bound, ordinary lower bound and frozen Target remain open.
