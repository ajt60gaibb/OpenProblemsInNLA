# MF-03 one-factor bidiagonal minor: independent final review

**Source author:** `/root/mf03_jt_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this exact partial combinatorial gate for aggregate import. Cauchy–Binet, the tableau bijection and frozen MF-03 Target remain open.

The exact mathematical/indexing statement was independently approved before implementation in `FINITE_PATH_CHAIN_INDEPENDENT_PRE_REVIEW.md`, against the author contract SHA-256 `1389c1e61c4f67388d996dc1990beca46cd9c833fd7909e9ec8cbdcb2e151bb8`. The frozen Lean source `lean-statements/NLA/Proofs/MF03/FiniteBidiagonalStep.lean` is SHA-256 `eecbfa6d99da058a8981f96b8b2eed649b23c23af5680df5bb8ddd67672efc7e`.

I read the complete source. `StrictRows m` is exactly a strictly monotone map from `Fin m` to `Fin (2m+1)`. `finiteStepWeight` is the product of the actual `finiteBidiagonal` entries along matching row/column positions; an independently compiled definitional expansion confirms each factor is `1` for a stationary step, `cosineFactor(k+1)` for an advance, and `0` otherwise. The proof expands the determinant, proves every nonzero matching permutation is monotone and hence identity, and retains sign `+1`. It covers arbitrary `m,k,X,Y`, including the empty `m=0` determinant. No proof escapes or new axioms appear.

Pinned Lean 4.33.1 direct module build passed 8,717 jobs. A separate imported exact-signature audit `/private/tmp/mf03-finite-bidiagonal-step-independent-audit.lean` (SHA-256 `9205fda548f2aee1838a06e997c8a008957af9943d78fccf5be083ef441f4c63`) checked the strict-row type, literal step-factor expansion, exact determinant theorem, and `#assert_trust kernel`. `#print axioms` returned only `[propext, Classical.choice, Quot.sound]`. Aggregate build is recorded in PR verification after import.

This one-factor identity alone does not give the finite Cauchy–Binet chain expansion, a weight-preserving tableau bijection, determinant positivity, all-order Padé coefficients, or the full Target.
