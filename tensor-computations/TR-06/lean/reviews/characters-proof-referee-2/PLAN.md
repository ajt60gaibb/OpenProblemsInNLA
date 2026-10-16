# Pre-proof finite-character algebra boundary

Let K be any algebraically closed field and A any finite-type commutative K-algebra. If its entire set of K-algebra characters A→K is finite, then A is a finite K-module. The statement allows nilpotents and the trivial algebra; it does not assume a domain, reducedness, finite prime spectrum, surjective characters, or a tensor interpretation.

Every maximal ideal m is the kernel of a K-character: the quotient A/m is a finite-type field algebra, hence algebraic/finite over K by the Jacobson version of Zariski's lemma, and IsAlgClosed.lift embeds it into K. The composite with the quotient homomorphism has exactly kernel m. Thus finiteness of characters gives finiteness of MaximalSpectrum A.

A is Jacobson because it is finite type over a field. Every prime ideal equals its Jacobson intersection of maximal ideals containing it. Therefore a prime is determined by the subset of the finite maximal spectrum containing it; this injects PrimeSpectrum A into a finite powerset. The spectrum is finite and Jacobson, hence discrete, and its Krull dimension is at most zero. Finite type makes A Noetherian; Module.finite_iff_krullDimLE_zero over the Artinian field K then proves the conclusion. This does not discard nilpotents, since the final Noetherian/artinian theorem controls them.

A more topological proof of the finite spectrum step may use density of closed points if a pinned theorem is convenient, with the same exact statement. No proof may assume finite complex solutions are definitionally a finite scheme fiber. The explicit conclusion will be used later on an actual fiber algebra, whose characters still need formal correspondence with the frozen tensor model.
