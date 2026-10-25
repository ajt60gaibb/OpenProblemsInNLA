# Reusable

## Module goal and place in the proof

This directory is the opt-in home for general-purpose results developed
alongside the Schiffer formalization but independent of its geometry, Bessel
analysis, and PDE construction.  `Schiffer.Reusable` is the umbrella entry
point.  The final counterexample does not use the result below; it is retained
as a standalone local reduction API for other developments.

## Files

- `ImplicitProductReduction.lean` packages the qualitative local
  Lyapunov--Schmidt reduction of a smooth map already written as
  `B × X → Y × Z`.  Given a base zero and invertibility of the partial
  derivative of the `Y` equation in the `X` direction, it constructs the
  canonical complement graph and reduced `Z` equation, proves their local
  smoothness and zero-set equivalences, and packages them as `Reduction`.
  This module does not find a Fredholm splitting or certify a common
  contraction radius; those are separate, application-dependent obligations.
