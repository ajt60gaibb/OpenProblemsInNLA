# RA-10 pinching reflection algebra: independent pre-implementation review

**Author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact staged matrix-algebra gate for Lean implementation.

I reviewed `NUCLEAR_PINCHING_REFLECTION_PRE_REVIEW.md` at SHA-256 `81a3da38ff88411c53b211b5c5231054a9a63aefb1193b43d4953cfeb9e61669` against the approved full nuclear pinching contract and source Equation (8). With the literal `U=P+P−I=2P−I`, symmetry `Pᵀ=P` gives `Uᵀ=U`; idempotence `P²=P` gives `U²=4P²−4P+I=I`, and therefore both orthogonality equations. For arbitrary real `P,M`, the noncommutative expansions of both `PMP+(I−P)M(I−P)` and `(M+UMU)/2` are `M−PM−MP+2PMP`. The exact factor `1/2`, multiplication order, `P=0`, `P=I`, and `n=0` cases are preserved.

Approval covers these definitions and algebraic equalities only. It does not prove any frozen nuclear-norm triangle, homogeneity, orthogonal invariance, or pinching contraction. The selected projection from `QAhat` still needs its own bridge. Freeze the implemented source for independent imported exact-signature and LeanCert kernel audit before aggregate import.
