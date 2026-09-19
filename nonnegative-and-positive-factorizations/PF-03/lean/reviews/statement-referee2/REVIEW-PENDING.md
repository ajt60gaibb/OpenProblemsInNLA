# PF-03 independent exact-source statement review

Reviewer: `/root/recover_lean_sources`, an AI agent, independent of statement
author `/root/recover_published_coverage`. This is the pre-proof fidelity,
numerical-interface, and computation-scope review required by the repository
protocol. It is neither human peer review nor an official Tau Ceti service run.

**Status: pending the coordinator's final successful exact-header run and
source-hash packet.** The mathematical/source review below has found no
required statement correction, but this document is not an approval seal.
The 25 `sorry` reference holes establish no theorem. No complete PF-03 Lean
verification, actual Comparator run, or count increment is claimed.

## Inputs and work actually performed

`INPUT-SNAPSHOT-MANIFEST.json` records the exact bytes read, including the
canonical statement, complete primary proof, both primary JSON data files,
actual Definitions/RawData/Challenge sources, numerical plan, generator,
Comparator configuration, dependency pins, and the repository review protocol
from commit `71563f17926cd826a892c2bba0e294894ee57a5c`. That protocol adapts
Tau Ceti Review revision `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`.

I read the source generator but did not execute or import it. My independent
`check_literals_and_obligations.py` parses the actual RawData Lean vector and
rational-literal syntax, compares all eight arrays with the two pinned primary
JSON files, and independently recomputes the finite obligations using Python
`Fraction` arithmetic and polynomial convolution reduced modulo X^3-2.
`INDEPENDENT-PREFLIGHT.json` records this actual execution and its input hashes.
It passed in about 0.28 seconds. It checks:

- the three strict rational root-endpoint inequalities;
- cache/column identity, both orthogonal Gram products, Q symmetry and trace;
- all seven restrictions, all seven exact kernel identities, fourteen strict
  local signs and the seven specified nonzero rational minors;
- the triangle and barycentric identities, positivity, and all 21 generators;
- every one of the 189 cross-block pairings and all 21 rational slice signs;
- the 25-contract sequence, deliberately unproved reference holes, absence of
  a Solution, and the Comparator permitted-axiom configuration.

This finite preflight is supplementary evidence, not Lean proof execution.
It does not certify the universal lemmas or substitute for their future proofs.
No Lean, Lake, Comparator, GitHub workflow, or author generator ran here.

## Complete original target

`SymMatrix` is the subtype of symmetric matrices. Its inherited topology over
the reals is the topology in the retained problem; `frontier (CPSet n)` is not
the frontier in the larger space of arbitrary, potentially nonsymmetric matrices.
`CompletelyPositive` allows every positive finite real factor width; the zero
matrix remains included through a one-column zero factor. `RationalFactor`
likewise allows every positive finite rational width. There is no bound by n,
rank, seven, or 444.

`RationalBoundaryFactorability` is the exact universal assertion for all n>=5.
C24 is an unconditional existential counterexample, and C25 is its exact
negation. Neither conclusion assumes a cone representation, seed certificate,
rank fact, successful numerical computation, or the desired conclusion.
The formalization may use a different finite witness order from the paper's
444-dimensional construction because the original target is universal. The
numerical plan explicitly declines the paper's additional order-444,
strict-positive-entry, and cp-rank-seven claims. That is an appropriate scope
restriction rather than a replacement of the original target.

## Contract-by-contract dependency and semantic review

| Contracts | Review finding |
|---|---|
| C01 | `Real.rpow 2 (1/3)` selects the positive real root; the cube equation, positivity and exact strict rational interval are all required conclusions. Actual kernel LeanCert endpoint proof terms must later be consumed in this chain. |
| C02-C03 | The explicit cubic product is correct. Independence is over all rational triples and must be proved, not supplied by a custom field instance or an evaluation oracle. |
| C04-C06 | The indexed rational columns really reconstruct the literal O data; both Gram orientations, Q symmetry/trace, local-cache equality, all seven kernel equations, fourteen signs and fixed minors remain obligations. Nothing accepts a stored PASS flag. |
| C07 | For a symmetric 3x3 H, the positive leading 2x2 block together with H*v=0 and v[2] nonzero gives the Schur-complement factorization and exactly the real span of v as kernel. The indispensable exact kernel equation is present. |
| C08 | One nonzero 2x2 rational minor is sufficient; rank three is unnecessary. If nonzero rational x=t*C*(1,alpha,alpha^2), then t is nonzero. Cross-multiplying any coordinate against a nonzero coordinate of x and using C03 makes all rows of C rationally proportional to x, forcing every 2x2 minor to vanish. Thus arbitrary real t and the zero cases are covered. |
| C09-C11 | Barycentric positivity/sum/evaluation and all cache identities are explicit. The generator order is `3*i+j`; the pinned `finProdFinEquiv` implementation was inspected and uses exactly quotient/remainder inversion. The 189 orientations suffice because Q symmetry supplies the reverse pairing. Slice signs are purely rational. |
| C12-C14 | Real cone coefficients are arbitrary nonnegative reals. The complete zero set includes zero via t=0. Local PSD and strict cross terms force a zero to use one group; C07 gives its seed ray and the first triangle coordinate or the positive slice gives t>=0. Rank-three injectivity of C_i is not needed. Rational zeros are then zero by C08. Salience is literal K intersect (-K)={0}, not the weaker library property called `Pointed`. |
| C15 | The explicit Fourier-Motzkin list retains zero-coefficient rows and every positive-negative pair. Its sign `a_p*A_q-a_q*A_p` is correct for inequalities `a_i*y+A_i*x>=0`. Empty, zero-only, positive-only and negative-only systems remain included. |
| C16-C17 | Eliminated variables range over all real vectors, not rational ones. Every retained coefficient is rational; arbitrary dimensions, zero variables and zero generators are admitted. Applying this to `x=V*lambda` and `lambda>=0` gives an exact whole-cone representation, not merely supporting halfspaces. |
| C18 | Literal salience implies the real kernel is zero, hence the rational kernel is zero and a rational left inverse exists. No square or invertible-R assumption is added. |
| C19 | The rational Gram transport is valid for every finite width. For P=RL, the discrepancy C-PC has zero Gram matrix using CC^T=RR^T and LR=I, so each rational sum of squares is zero. This yields RLC=C and LCC^TL^T=I. The zero-dimensional generic cases do not weaken the fixed-dimensional final application. |
| C20-C21 | The trace sum includes every column at unrestricted width. The finite sum of nonnegative values is zero, so every column is a rational cone zero and vanishes, contradicting XX^T=I_7. Representation and real-kernel premises are internal and must be discharged before C24/C25. |
| C22 | Exactly five zero rows are appended. The specified zero diagonal and actual nonnegative real Gram factor are proved, along with preserved cone representation and kernel. This produces an admissible order at least five without facet enumeration. |
| C23 | A completely positive matrix has nonnegative diagonal. Perturbing the selected zero diagonal in the negative direction, inside the symmetric subtype, proves non-interiority; existing membership supplies closure membership. No erroneous ambient-space boundary shortcut is present. |
| C24-C25 | All internal numerical, algebraic, geometric and representation hypotheses are discharged. These are the full original-target conclusions, not partial helpers or tautological conditional assertions. |

## Computation reduction, reuse and attribution

The route avoids the 54,264-subset facet search, any 444-by-444 Gram expansion,
rank-three certificates, redundant reversed pairings, and factor-width search.
The omitted work is replaced by genuine universally quantified theorem
obligations (especially C15-C19); no numerical oracle or extra final premise
takes its place. The exact 40-digit isolating interval already makes every
required finite sign strictly positive in this independent preflight. There
is no reason to enlarge it or introduce more expensive precision now.

The transparent Definitions/Challenge split and fixed Comparator names make
the target auditable. The source documents the previously consulted Schiffer
and Forsythe structural examples and preserves their role as examples, without
claiming to import their unrelated mathematical results. The generic matrix
symmetry facts used in subtype constructors are existing library facts; no
substantive PF-03 theorem is smuggled into Definitions.

Sidney Holden retains mathematical/seed authorship and the Flatiron affiliation.
George Stepaniants receives formalization credit with the Department of
Computing and Mathematical Sciences, California Institute of Technology.
The inspected attribution fields contain no published email address.

## Gates still outstanding

This review must be finalized against the exact successful header-run hashes.
Any semantic source change requires explicit re-review; an import-only repair
may be checked through a bounded amendment with new hashes. The current
candidate still contains no substantive Lean proof. Future approval requires
real kernel-mode LeanCert consumption, local proof compilation, transitive
axiom/trust checks, two independent final proof reviews, actual published-source
Linux Comparator/kernel/sandbox checks, and truthful schema-valid
`formalization.yaml`. The absent final metadata and Solution are expected at
this statement-only phase and are not being marked complete.
