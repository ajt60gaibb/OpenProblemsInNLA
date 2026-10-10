# SP-14 off-diagonal block polynomial: independent pre-proof review

**Reviewer:** `/root`, 9 October 2026. **Verdict:** APPROVE the frozen `BASE_OFFDIAGONAL_CHARPOLY_PRE_REVIEW.md` contract for implementation. Its theorem is a generic complex-polynomial identity, including `m=0` and the spectral parameter `X=0`; it is a finite algebra component, not the final SP-14 counterexample.

The proposed matrix has block sizes `(m+1)×(m+1)`, `(m+1)×m`, `m×(m+1)`, and `m×m`, so the full matrix has size `2m+1`. The product `C B` has size `m×m`. Thus `X·χ_(CB)(X²)` has degree `1+2m` and the correct orientation. For nonzero complex `z`, the Schur complement of `zI_(m+1)` in `zI−[0 B; C 0]` is `zI_m−z⁻¹CB`; its determinant simplifies to `z·det(z²I_m−CB)`. The signs of both off-diagonal blocks are negative before multiplication, so their product has the positive sign inside the subtraction. At `m=0`, the formula is `X= X·1`; at `m=1`, it is `X³−(CB)₀₀X`.

The proposed nonzero-evaluation proof must use infinitely many complex values to conclude polynomial equality at every value, including zero. It may use an equivalent polynomial-ring determinant proof, but the exact displayed theorem signature, unrestricted `B,C`, all natural `m`, and value at zero must remain intact. There is no eigenvalue-list or diagonalizability premise. Applying this identity to the actual Toeplitz section still needs the reviewed parity theorem plus a proof of the base symbol's full frozen Fourier pattern; neither is supplied by this contract.

| Reviewed input | SHA-256 |
| --- | --- |
| **`BASE_OFFDIAGONAL_CHARPOLY_PRE_REVIEW.md`** | **`c8913cf163d7c31f5927e218d8bbd370a869a80f222e1db6ad55fce10c33fbcd`** |
| Frozen `NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `BASE_ACTUAL_TOEPLITZ_PRE_REVIEW.md` | `0760870797779a198c7fd16e4b1af8d06a398d9384ede2dc20c058a2881674e9` |

Changed contract bytes reopen this pre-proof review.
