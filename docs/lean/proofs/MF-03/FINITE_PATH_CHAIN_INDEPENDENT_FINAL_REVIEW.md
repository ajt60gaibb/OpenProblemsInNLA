# MF-03 literal finite valid-path chain expansion: independent final review

**Source author:** `/root/mf03_jt_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this exact finite chain gate for aggregate import.

The mathematical/indexing contract `FINITE_PATH_CHAIN_PRE_REVIEW.md` is SHA-256 `1389c1e61c4f67388d996dc1990beca46cd9c833fd7909e9ec8cbdcb2e151bb8` and was independently approved before implementation. The frozen source `lean-statements/NLA/Proofs/MF03/FinitePathChain.lean` is SHA-256 `33607688166f0ef956360b026cd24cc08d0fe9815a0496eabe3753682a0bb09e`.

I checked that `finiteBidiagonalProduct m N` is expanded into a dynamic chain whose first transition for `N+1` factors uses label `N`, then `N−1,…,0`. The theorem derives the determinant identity by the audited one-step Cauchy–Binet theorem and exact one-factor minor weights. `FiniteValidPath m N X Z` is an actual recursively encoded sequence of strictly increasing positions with every coordinate staying or advancing one site at each step. Its weight uses the same descending labels. The source proves invalid transitions have zero weight, then proves the dynamic sum equals the literal finite sum over valid paths. This includes `N=0`, `m=0`, equal and unequal endpoints, with no factorial or extra path choice.

The direct pinned Lean 4.33.1 build passed. My separate imported exact-signature audit `/private/tmp/mf03-finite-path-chain-independent-audit.lean` is SHA-256 `1f564edf4049a3527c6dc1e630923079fda10df92c5d93e6af35f58faf870d25`; it checked the valid-step definition, literal path sum, dynamic determinant theorem, bridge equality, and final valid-path determinant theorem with LeanCert `#assert_trust kernel`. The final theorem's transitive axioms were exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no proof escape. Changed source bytes require a new review.

This theorem does not yet provide the endpoint path/tableau bijection, exact tableau weights, determinant positivity, all-order Padé pairs, or frozen MF-03 `Target`.
