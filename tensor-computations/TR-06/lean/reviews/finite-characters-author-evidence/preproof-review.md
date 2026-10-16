# Independent pre-proof review: finite-character algebra

Reviewer: infrastructure/area subagent, not the proposed proof author. APPROVE exact `/private/tmp/tr06-proof-root/NLA/TR06/FiniteCharactersBoundary.lean`, SHA256 `b9499d16fae846b19fc71d3da224f5eae60cd904cc04e921a5eb9d1dd2ca2a1b`.

Independently read the full statement and FINITE_CHARACTERS_PLAN.md, checked pinned Jacobson, Nullstellensatz, algebraically-closed lift, and quasi-finite APIs, and typechecked an exact copied statement locally (proof-area evidence log087). Finitely many K-algebra characters of an arbitrary finite-type commutative algebra over an algebraically closed field do imply module finiteness. Every maximal ideal is a character kernel by Zariski's lemma and a field embedding into K. The algebra is Jacobson, so finite closed points force the entire spectrum finite and discrete; finite type also gives Noetherianity, and the Artinian/dimension-zero criterion yields finite-dimensionality. The proof does not assume away nilpotents. The zero algebra is allowed and yields an empty spectrum and a finite zero module.

A smaller pinned implementation route exists: `JacobsonSpace.discreteTopology` directly accepts finiteness of `closedPoints`, so the prime-to-powerset injection can be omitted. Use `PrimeSpectrum.isClosed_singleton_iff_isMaximal` to identify the maximal points, then `PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero` and `Module.finite_iff_krullDimLE_zero`. This is the same approved mathematical boundary, not a hypothesis change.

The theorem makes no claim that a tensor point fiber is definitionally a scheme fiber; the algebra/point correspondence and generic-point quasi-finiteness remain separate obligations.
