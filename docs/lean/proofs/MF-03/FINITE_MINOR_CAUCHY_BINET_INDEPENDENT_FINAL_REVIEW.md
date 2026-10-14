# MF-03 finite minor Cauchy–Binet: independent final review

**Source author:** `/root/mf03_jt_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this exact finite combinatorial gate for aggregate import.

The mathematical and indexing contract `FINITE_PATH_CHAIN_PRE_REVIEW.md` is SHA-256 `1389c1e61c4f67388d996dc1990beca46cd9c833fd7909e9ec8cbdcb2e151bb8` and was independently approved in `FINITE_PATH_CHAIN_INDEPENDENT_PRE_REVIEW.md` before implementation. The frozen source `lean-statements/NLA/Proofs/MF03/FiniteMinorCauchyBinet.lean` is SHA-256 `0b6793e6ea3ff6834e866e96957f9c28a1b6725fda73c119ca81f1fbb06606d8`.

I checked the public theorem for arbitrary real matrices indexed by `Fin (2m+1)` and all `m`, with strictly increasing `X,Z : Fin m → Fin (2m+1)`. Its left side is the determinant of the exact product minor; the right side sums `det A[X,Y]·det C[Y,Z]` once over each strictly increasing `Y`. The source first expands over all intermediate maps, proves repeated-column determinants vanish for noninjective maps, and constructs an equivalence between injective maps and pairs of a sorted `Y` with a permutation. The determinant sign of the permutation is absorbed into the second minor. Thus no factorial multiplicity or extra matrix hypothesis remains. The empty case `m=0` is included.

The direct pinned Lean 4.33.1 build passed. My separate imported exact-signature audit `/private/tmp/mf03-finite-minor-cauchy-binet-independent-audit.lean` is SHA-256 `40ff35e80e8ae235098faf009b6e88fb60bef2a5ba34176d2e7a9631f32c8183`; it checked the all-map, injective-map, and final sorted-map signatures, with LeanCert `#assert_trust kernel`. The final theorem's transitive axioms were exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no proof escape. Changed source bytes require a new review.

This one-step identity does not yet construct the finite labelled path-chain expansion, the weight-preserving tableau bijection, determinant positivity, all-order Padé pairs, or frozen MF-03 `Target`.
