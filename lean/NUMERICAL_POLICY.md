# Numerical certification guidance

Use this file only when the Lean theorem has a nontrivial theorem-bearing
numerical or computer-assisted component.

The objective is a sound, auditable proof—not compliance with a fixed numerical
workflow. LeanCert is available as a certified option, but exact Lean reasoning,
a custom proved checker, or another sound method may be better.

## Good default order

When useful, try the following before enlarging a certified computation:

1. make the mathematical statement and exact domain clear;
2. search Mathlib and LeanCert for an existing result;
3. simplify symbolically and separate analytic from numerical content;
4. use symmetry, monotonicity, convexity, substitutions, scaling, or endpoint
   arguments to reduce dimension or domain;
5. certify only the residual actually needed by the theorem; and
6. name and reuse a certified lemma rather than repeating equivalent work.

This is guidance, not a prohibition on direct computation. A finite or interval
verification of the necessary scope is legitimate when it is the clearest or
most reliable proof. Do not demand extra elegance at the expense of correctness,
and do not expand brute force merely because computation is easier than
understanding the domain.

## LeanCert and trust

Kernel-checked retained proofs are preferable when practical, for example:

```lean
by
  leancert (trust := kernel)
```

A broader trust mode may be used when the current Goal permits it and kernel
checking remains disproportionate after reasonable optimization. Record the
actual additional trust only when it matters to the completion claim. Never call
something “machine checked” while hiding a material trust dependency.

## External computation

External programs may search for witnesses, partitions, candidate bounds, or
certificates. Their output remains untrusted until Lean checks the relevant
claim through a proved parser/checker, an exact theorem, or a sound certified
interface.

When exact input data comes from `../proof/`, preserve a stable relative path and
record the file and theorem dependency when it actually enters the proof. Keep
derived Lean code and minimal checked certificate artifacts under
`ProofProject/`.

## Failure discipline

A failed interval or certificate search does not by itself refute the theorem.
Reconsider the formulation, domain, scaling, decomposition, and analytic
reductions before merely increasing computational scope. Conversely, do not
abandon a mathematically necessary computation just because it is substantial.
