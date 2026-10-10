# TR-14 middle catalecticant rank: independent mathematical pre-review

**Reviewer:** `/root/tr14_frob_review` (independent AI agent), 10 October 2026. **Verdict:** APPROVE the frozen normalized-chart rank contract. The original-coordinate result is approved as a subsequent bridge **provided** the full all-degree `GL₂` apolar transport from the approved quotient contract is proved; the displayed middle-degree pairing identity alone cannot establish preservation of the least apolar degree. No Lean implementation was performed in this review.

| Reviewed input | SHA-256 |
| --- | --- |
| **`MIDDLE_CATALECTICANT_PRE_REVIEW.md`** | **`b72a9a0e25358fbe2b41dff423c638c03202bc367d6153cf4f08c0e1fb054981`** |
| Canonical `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| Canonical `tensor-computations/TR-14/solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66c282716c14bc6` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Audited `ApolarMinimal.lean` | `0e98ae3b414d2130bebe7470a25c7c8b3e422225b5581ae4b93d036f39f520d9` |
| Audited `NormalizedQuotient.lean` | `3c6809e84eb522ad82c28f49245b80ef6da7da84cd201f46f4cbfb54a363a54d` |
| Audited `FrobeniusMinimal.lean` | `dca235b899ba5729e5bdfb50986e55836989c2736b133ee6e2b4a7f428dee29e` |

## Normalized rank check

Set `a=⌊D/2⌋`, `b=D-a=⌈D/2⌉`. The actual matrix has row indices `0,…,a`, column indices `0,…,b`, and entries `h_{i+j}`; `i+j≤a+b=D` proves every moment index is present. For column vectors `c,d`, expanding `λ((∑c_i t̄^i)(∑d_j t̄^j))` and applying the audited all-moment equality at each `i+j` gives exactly `cᵀ C_h d`, with no complex conjugation.

The audited minimality bound gives `r₀−1≤a≤b`. Thus both `ρ_a` and `ρ_b` hit every member of the quotient power basis and are surjective. The audited Frobenius theorem makes `A→A*`, `x↦(y↦λ(xy))`, injective; finite dimension `r₀` makes it an isomorphism. The matrix map factors as `ρ_b* ∘ B ∘ ρ_a`. Here `ρ_a` is onto, `B` is an isomorphism, and `ρ_b*` is injective, so its rank is exactly `dim A=r₀`. This also justifies the rectangular odd-`D` case. No genericity, distinct-root, or nonzero determinant of the rectangular matrix is assumed.

At the balanced endpoint `D=2r₀−2`, both sides have degree `r₀−1`, both quotient maps are isomorphisms, and the square middle matrix has full rank `r₀`. At the general finite endpoint `D=1`, the least degree is `r₀=1`, the matrix is the nonzero row `[h₀,h₁]`, and its rank is one; the degree-zero and degree-one quotient maps are respectively an isomorphism and a surjection. The zero moment vector is correctly excluded from the quotient theorem and has a zero middle matrix separately.

## Chart transport obligation

For `φ_T` acting on homogeneous forms and `L'_D=L_D∘φ_T⁻¹`, multiplication compatibility gives `L'_D((φ_TP)(φ_TQ))=L_D(PQ)` whenever the degrees of `P,Q` sum to `D`. In degrees `a,b`, if `M_a,M_b` represent the invertible actions, then `C_{h'}=(M_a^{-1})ᵀ C_h M_b^{-1}` in the corresponding monomial bases; hence ranks agree. This uses ordinary transpose, never a conjugate transpose.

**Required implementation clarification:** this middle-degree matrix relation does not by itself show that the transformed `g` is still least-degree apolar. Before applying the normalized theorem with the original `r₀`, the chart development must prove the same pairing identity for **every** split `d+(D-d)=D`, carry every apolar kernel by an invertible degree-`d` map, show `h'≠0`, and normalize a nonzero least apolar form to monic exact degree `r₀`. These are explicitly required by the previously approved `QUOTIENT_FROBENIUS_PRE_REVIEW.md`; they must remain part of this rank bridge, not become assumptions in `NLA.Statements.TR14.Target`.

The normalized rank theorem may be implemented first and reported as conditional progress. The original-coordinate theorem requires the chart bridge. Neither result proves any all-width equality. Frozen Lean sources still require separate exact-signature, proof-escape, imported LeanCert kernel, and transitive-axiom review. Changed contract or source bytes reopen this review.
