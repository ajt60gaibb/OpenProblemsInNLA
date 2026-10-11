# MF-03 generic reduction: independent pre-proof review

**Reviewer:** `/root` (AI agent), 9 October 2026. **Verdict:** APPROVE the precise conditional theorem in `REDUCTION_PRE_REVIEW.md` for Lean implementation. This is a review of the mathematical contract before code, not a review of any later Lean proof or the full MF-03 target.

The contract starts from an actual `NormalizedPadeRepresentation m P Q`, so `Q(0)=1` and the degree-zero convolution forces `P(0)=1`. Both polynomials are nonzero. For `D=gcd(P,Q)` and quotients `P₁,Q₁`, the factorization `Q=D Q₁` gives `D(0) Q₁(0)=1`, hence `c=D(0)≠0`. Multiplying **both** quotients by the constant polynomial `C c` restores denominator normalization: `(C c Q₁)(0)=1`. This scaling direction is correct. Divisibility and nonzero factors retain degree at most `m`; `isCoprime_div_gcd_div_gcd` and invariance under nonzero constant units give the reduced pair. The cross-product `Pᵣ Q=P Qᵣ` follows from the common factors and retains the approximant even where either denominator vanishes.

For the exact Padé coefficient conditions, the proposed formal series has coefficient `1/(2j)!`, matching the frozen statement. The original conditions say the coefficients of `QF−P` vanish for every index **through `2m` inclusive**. Since `QF−P=D(Q₁F−P₁)`, induction on the product coefficient works: all terms involving a positive degree of `D` use a previously vanished coefficient of the parenthesized series, while the remaining term is `D(0)` times its current coefficient and `D(0)≠0`. Constant scaling then retains zero coefficients. No analytic limit, radius restriction, or unproved Padé uniqueness is needed for this implication. The resulting theorem supplies reduced existence only when a normalized pair is already available; it does not assert the still-missing all-order source formula or disk estimate.

## Bound inputs (SHA-256)

| Input | SHA-256 |
| --- | --- |
| **`docs/lean/proofs/MF-03/REDUCTION_PRE_REVIEW.md`** | **`331d29fb2c700a53dee761fe27adcda91bcb383c08481d5da4557800fd208d37`** |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `lean-statements/NLA/Proofs/MF03/Uniqueness.lean` | `c781644e76a6143535a45862263e6776ee1257ff6ac2d69eed328dd63f73daa5` |
