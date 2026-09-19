# PF-03: independent review of the actual statements

Reviewer: `/root` (AI-assisted review, not human peer review). The statement
author is `/root/recover_published_coverage`. I authored no PF03 definition,
reference contract, numerical data generator, or proof. I independently read
the retained original question, its complete primary proof, the numerical plan,
the actual 25 Lean reference declarations, definitions and Comparator map.
I reviewed the two author amendments: corrected import names and a generic
rectangular Gram symmetry proof plus the intended matrix topology import.

**Pending the final successful header elaboration and immutable hash seal.**
There is no substantive PF03 Lean proof yet. The deliberate reference `sorry`
holes are not verification evidence.

## Fidelity to the original problem

The target is the universal rational factorability assertion for rational
completely positive matrices on the boundary, at every order at least five.
The topology is explicitly that of the real symmetric-matrix subtype. A
boundary in all matrices would give a spurious shortcut and is not used.
Both factor definitions permit every positive finite width; no rank-seven or
dimension-dependent width restriction is introduced. The zero matrix is still
allowed through a one-column zero factor.

C24 asserts a counterexample without certificate, representation, rank,
successful-computation or other unproved hypotheses. C25 negates the unchanged
universal statement. The construction via an unspecified finite rational
halfspace representation, padded with five zero rows, can refute this target
without verifying the primary paper's extra order-444 and strict-entry claims.
Those extra claims are expressly excluded from this formalization's scope.

## Numerical statements and finite data

I inspected the transparent rational/cubic data translation without running it
as my independent check. My separately written `check_literals.py` parses the
actual Lean array syntax, compares all 802 rational entries against the two
pinned primary JSON files, and checks the strict cube endpoints and the seven
fixed nonzero two-by-two minors with exact rational arithmetic. The actual run
is recorded in `LITERAL-CHECK-RUN.json` and its output in `LITERAL-CHECK.log`.
It passed. This is a supplementary Python check, not a Lean or Comparator run.

C01 requires the positive cube root and both strict rational bounds. Kernel
LeanCert results must actually feed this theorem and the later sign proofs.
C02-C06 retain the cubic evaluation operations, rational linear independence,
literal orthogonal-matrix identification and both Gram orientations, Q's
symmetry and zero trace, all seven restrictions/kernel equations, fourteen
strict local signs and seven nonzero minors. The stored entries are data, not
assumptions that their checks succeeded.

The fixed interval of width 10^-40 is sufficiently precise for the independent
finite preflight; the proof need not enlarge it. Exact rational arithmetic
should handle algebraic identities, reserving interval arithmetic for signs.

## Universal obligations and edge cases

- C07 is mathematically sufficient: a symmetric three-by-three form with
  positive leading two-by-two block and H*v=0, v[2] nonzero, has the required
  Schur-complement factorization and precisely the line through v as kernel.
- C08 needs only one nonzero two-by-two rational minor. If a rational nonzero
  vector is a real multiple of C*(1,alpha,alpha^2), cross multiplication with
  a nonzero coordinate and C03 makes every row of C proportional to it over
  the rationals, contradicting that minor. Zero scalars and vectors remain.
- C09-C11 include the triangle/cache and barycentric identities, positivity,
  all 21 generator identifications, all 189 cross-block signs, and the 21 slice
  signs. Index order is fixed by the actual `finProdFinEquiv`. Symmetry gives
  the reversed pairings, so checking those again is unnecessary.
- C12-C14 concern arbitrary nonnegative real coefficients, not rational cone
  coefficients. Local PSD and strict cross terms force a zero to lie in one
  block. The kernel theorem gives its line; the first triangle coordinate or
  positive slice makes its scalar nonnegative. Rank three of each C is not
  needed. `NoLine` is literal salience, not a weaker library convention.
- C15 keeps zero-coefficient inequalities and all positive-negative pairs.
  The expression a_p*A_q-a_q*A_p has the right sign for inequalities >=0.
  Empty and one-sided systems are included. C16 eliminates arbitrary real
  variables while keeping rational coefficients. C17 must prove the exact
  whole-cone equality; no facet or elimination oracle is accepted.
- C18 derives the real zero kernel and a rational left inverse from salience.
  It assumes neither a square representation nor invertibility of a selected
  minor. Generic zero-dimensional cases do not remove the fixed seven-
  dimensional contradiction in the final application.
- C19 quantifies over every finite width. With LR=I and CC^T=RR^T, the matrix
  C-RLC has zero Gram matrix, hence vanishes by rational sums of squares.
  This proves actual Gram transport rather than merely equal ranks.
- C20-C21 sum every column's quadratic value. Nonnegativity, zero trace and
  the rational-zero theorem force every transported column to vanish,
  contradicting XX^T=I_7. All intermediate premises must be discharged.
- C22 appends five zero rows and proves the real nonnegative factor and a zero
  diagonal. C23 uses continuous negative diagonal perturbations inside the
  symmetric subtype; membership supplies closure membership. It does not
  incorrectly assume the entire CP cone is closed to obtain this boundary.
- C24-C25 discharge all of these internal obligations. No partial helper or
  special dimension result may be counted as a complete problem.

## Computation, review protocol and publication requirements

The chosen generic Fourier-Motzkin route replaces the 54,264-subset facet
enumeration and a 444-by-444 expanded Gram computation with real mathematical
proof obligations. Rank-two minors replace unnecessary rank-three checks.
No hypothesis is weakened in exchange for these reductions.

I applied the repository's statement/fidelity/axiom review guidance from
`docs/lean/REVIEW.md` at 71563f17926cd826a892c2bba0e294894ee57a5c,
which pins Tau Ceti revision afb424eda89e8ac96d9eb69f6a88972055a4cd1b.
This is an adapted manual review, not an official Tau Ceti service execution.
Previously consulted Schiffer and Forsythe projects serve as layout and
verification examples, not sources of a PF03 theorem.

The Comparator map lists the exact 25 independent reference declarations and
restricts axioms. Actual Comparator, sandbox, negative-control and published-
commit kernel checks remain future GitHub Linux work. Header elaboration only
checks that the definitions/types are accepted. Neither it nor these two
statement reviews verifies the future proof bodies.

Original mathematics and numerical data remain credited to Sidney Holden,
Flatiron Institute, Simons Foundation. Formalization credit is George
Stepaniants, Department of Computing and Mathematical Sciences, California
Institute of Technology. The inspected credits publish no email.

Final proof reviews by two nonauthors, local proof compilation, consumed
kernel LeanCert checks, actual GitHub verification, truthful schema-valid
formalization.yaml and an upstream per-problem PR remain required. This
review changes no completed-problem count.
