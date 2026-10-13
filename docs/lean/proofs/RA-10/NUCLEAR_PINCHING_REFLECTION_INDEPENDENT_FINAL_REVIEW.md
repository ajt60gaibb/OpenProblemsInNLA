# RA-10 pinching reflection algebra: independent final review

**Source author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this exact matrix-algebra partial gate for aggregate import.

The source-locked staged contract `NUCLEAR_PINCHING_REFLECTION_PRE_REVIEW.md` is SHA-256 `81a3da38ff88411c53b211b5c5231054a9a63aefb1193b43d4953cfeb9e61669` and was independently approved before implementation. The frozen source `lean-statements/NLA/Proofs/RA10/PinchingReflection.lean` is SHA-256 `262f37c9ecb1a10bd551bf1600cc4f15c0bbd344577198a0f528b0cbd393d829`.

I checked the exact definitions `reflection P=P+P−I` and `pinch P M=PMP+(I−P)M(I−P)`, without symmetry or idempotence hidden in either definition. Under `Pᵀ=P`, the reflection is symmetric; under `P²=P`, its square is the identity; together these yield both orthogonality equations. For arbitrary `P,M` and every `n`, the public equality is exactly `pinch P M=(1/2)•(M+reflection P*M*reflection P)`, preserving the noncommutative order and exact half factor. It includes `n=0` and arbitrary nonsymmetric `M`.

The direct pinned Lean 4.33.1 build passed. My separate imported exact-signature audit `/private/tmp/ra10-pinching-reflection-independent-audit.lean` is SHA-256 `ebd735d091ef8ee970b7cd85c8fae0aa4a5ed87df9ca2a36fafe9e5cb8acec6f`; it checked both definitions and all four theorem signatures with LeanCert `#assert_trust kernel`. Both axiom reports were exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no proof escape. Changed source bytes require a new review.

The frozen nuclear norm's triangle, homogeneity, orthogonal invariance, coefficient-one pinching contraction, matrix transfer, and RA-10 `Target` remain open.
