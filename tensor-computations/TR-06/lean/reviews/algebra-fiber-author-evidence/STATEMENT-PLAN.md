# Proposed finite-generator character bound

Exact intended supporting statement: let R,A be commutative rings, let K be a
field, with R-algebra structures on A and K. If g:Fin N→A spans A as an R-module,
then every finite set q of R-algebra homomorphisms A→K has q.card≤N.
No freeness or field structure is assumed on A or R, and N=0 is allowed.

The evaluation map Hom_R(A,K)→(Fin N→K), h↦(j↦h(g_j)), is K-linear and injective
because the g_j span A. Distinct algebra homomorphisms are K-linearly independent
in Hom_R(A,K), by Mathlib's Artin independence lemma. Their evaluation vectors
are therefore independent in K^N, giving the finite-cardinality bound.

This is uniform over the choice of R-algebra structure on K, which is useful
for finite algebraic envelopes evaluated at varying base points. It does not
construct a finite envelope, identify a tensor fiber with characters, or prove
any geometric/semialgebraic fiber bound. Those bridges remain separate.
