# TR-14 moment-to-quotient mode pairing: independent pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen exact contract for implementation. It is an all-moment multilinear bridge, not a CRT, symmetric width, or frozen Target proof.

| Reviewed input | SHA-256 |
| --- | --- |
| `MOMENT_QUOTIENT_MODE_PAIRING_PRE_REVIEW.md` | `d9c791805617767bc2cf2d933a9d83ed9b188c6f6de614ee7f697d5d93d4f114` |
| Canonical `solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Frozen `NLA.Statements.TR14` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Audited `NormalizedQuotient.lean` | `3c6809e84eb522ad82c28f49245b80ef6da7da84cd201f46f4cbfb54a363a54d` |
| Audited `GL2HankelMode.lean` | `5b700ce0fbd05cfa39f047830b6455dc64cc361acfe3218f667d2af9f09e02c2` |

The affine mode polynomial `p_v(t)=Σ_{i=0}^q v_i t^i` is the source's zero-based coordinate polynomial, with no combinatorial weights. Its quotient image is exactly evaluation at `τ=AdjoinRoot.root g`, so the future Lean definitions cannot change the mode semantics. Expanding the product of the `m` quotient sums gives one term for each function `i:Fin m→Fin(q+1)`. The quotient algebra is commutative, hence each monomial is `τ^(Σ_k i_k)`. The sum of indices lies in `0,…,D=mq`, exactly the domain of the stated all-moment hypothesis; applying the complex-linear functional yields the frozen `HankelIndex` coefficient and its tensor contraction. No quotient evaluation at an arbitrary complex number occurs.

The endpoint ledger checks: `m=0` has one empty index tuple and becomes `Λ(1)=h₀`; `q=0` has only zero mode indices and gives `h₀∏_k u_k(0)`; the top tuple `(q,…,q)` reaches `h_D`. These include `m=3,q=1,2` examples in the contract. The existing `quotientMomentFunctional_all` has exactly the proposed monicity, degree, and recurrence premises and supplies the full `0≤j≤D` identity; there is no need to assume Frobenius nondegeneracy or `r₀≤q+1`. The bridge is valid even when quotient reduction lowers a polynomial representative's degree, because the all-moment identity evaluates powers **after** reduction.

The implementation should prove the product-of-sums identity and use the existing frozen `Hankel` definition, keeping the full all-moment premise and the top degree. A theorem matching only initial moments would fail this review. CRT/local factorization, the symmetric upper bounds, arbitrary ordinary lower bound, and full TR-14 Target remain separate obligations.
