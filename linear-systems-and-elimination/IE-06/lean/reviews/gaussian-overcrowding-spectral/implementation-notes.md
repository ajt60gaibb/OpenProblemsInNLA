# Implemented deterministic spectral-to-minor implication

The coordinator approved `../gaussian-overcrowding-spectral-contract.md`
before implementation. The exact generic core theorem is
`singular_event_implies_large_inverse_gram_minor`. It produces a finite subset
of exactly r row labels and the literal subtype determinant threshold
(t^(2r))⁻¹ / choose(m,r). The Gaussian stochastic assembly owns the separate
square-matrix dimension substitutions and almost-sure Gram positivity.

All substantive bridges are proved. Row restriction compares the actual
forward singular values on a common Euclidean input space. The inverse-Gram
lower quadratic form comes from the actual adjoint and Gram inverse identity,
with Cauchy–Schwarz and the strictly positive threshold. The forward trailing
Gram subspace constructs a row-space subspace of dimension at least r;
min–max then bounds the rth sorted inverse-Gram eigenvalue.

The principal-minor sum is proved equal to the spectral product sum by
characteristic-polynomial equality with the actual diagonal spectral matrix,
using Mathlib's proved principal-minor coefficient identity. One product of
r eigenvalues supplies the required bound; positivity of every eigenvalue
controls all remaining products. Finite averaging uses exactly choose(m,r)
subsets. No principal-minor identity, inverse ordering claim, adjoint singular
value identity, or stochastic estimate is assumed.

All 11 local declarations are individually checked by LeanCert in kernel
mode and have printed axiom closures; only the three standard foundational
axioms occur. The frozen source hash and direct pinned-cache compilation log
are in `receipt.json` and `compile.log`. The compilation has no warnings.
