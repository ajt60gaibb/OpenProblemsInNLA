# PF-03 numerical and semantic statements before proofs

This restates the already reviewed pre-code numerical plan, whose recovered
SHA256 is d6e1414fcbafd435d56ef625929168d99763c9660346fe8735f32cb87b1477db.
The mathematical packet received two nonauthor approvals before these Lean
headers were written. The exact new headers still require root elaboration and
two independent source reviews. No numerical certificate or proof has been run
for this new draft.

## Complete target and attribution

The final statement is the negation of the original PF-03 assertion: every
rational symmetric completely positive boundary matrix of order at least five
has a nonnegative rational Gram factor of some positive finite width.
Factor width is unrestricted. Frontier is computed inside the real symmetric
matrix subtype with its inherited Euclidean topology.

Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons
Foundation, supplied the complete mathematical argument and exact cubic-field
seed. George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, contributes the formalization and proof
engineering with Codex assistance. No new mathematical priority is claimed.

The source is immutable upstream commit
fd6dec765e49002e52e7c38663bbf1fbd50a9ecc, with primary source bytes unchanged at
71563f17926cd826a892c2bba0e294894ee57a5c. The original proof is
references/holden-pf03-2026-09-13/proof/PF03_counterexample.tex, SHA256
0a4a17a034460f26a6e58a91bb1a47b6ef56ebc064a97b5d3fb9f7cf0e8a9064.

## N01: root, endpoints and actual LeanCert consumption

Define alpha as Real.rpow 2 (1/3). Prove its exact cube equation, positivity
and the strict enclosure in C01:

    ell = 12599210498948731647672106072782283505702 / 10^40
    upp = 12599210498948731647672106072782283505703 / 10^40
    alpha^3 = 2, 0 < alpha, ell < alpha < upp.

Closed endpoint obligations are 0 < ell, ell^3 < 2 and 2 < upp^3. Future
proofs must use the pinned LeanCert kernel path for the appropriate endpoint
certificates and consume those proof terms through root monotonicity, finite
sign bounds and the final original-target theorem. Merely importing LeanCert,
or proving an unrelated scalar fact, does not meet this requirement.

The toolchain is Lean 4.33.1, Mathlib
0df444a360eaa60ab8c11dca51a86af692955474, and LeanCert
621a43d7cf21f87872392a01e874f2f1dbddc926. The future numerical modules must set
kernel trust and use explicit kernel-mode interval tactics; native_decide and
native-execution axioms are forbidden. All exported proof declarations must
pass transitive permitted-axiom and kernel-trust checks.

## N02: exact cubic identities

For rational triples, evaluation is a+b*alpha+c*alpha^2. The explicit product is

    (a,b,c)*(d,e,f) = (ad+2bf+2ce, ae+bd+2cf, af+be+cd).

C02 proves its evaluation law; C03 proves independence of 1, alpha, alpha
squared over the rationals. These are theorems, not field-instance assumptions.

The literal source JSON hashes are:

- exact_algebraic_certificate.json:
  868486419ebe5710e0e38aafcf776ae9d22533c4adc9c7dce85e6ff99a9ead01.
- rational_cone_certificate.json:
  e4543a34d630be63abe8141a08976559f11fd85346c58939ab6115378040d5f9.

RawData merely encodes those rational strings. Every stored O, H, triangle,
barycentric or generator cache must agree with its defining expression in a
Lean theorem; the generator's byte checks establish no mathematical equality.

C04 checks O*O-transpose=I once and derives the reverse orientation abstractly.
C05 checks symmetry and trace zero of Q. C06 checks all seven restricted-form
identities, their kernel vectors, and the seven exact rational minors
C_i[0,0]*C_i[1,1]-C_i[0,1]*C_i[1,0] are nonzero.

The minor positions are the seven witnesses printed by the original exact
preflight at historical execution chunk 730603. No new minor search has been
run for this draft.

## N03: seven local forms

C06 requires the fourteen strict signs

    H_i[0,0] > 0
    H_i[0,0]*H_i[1,1] - H_i[0,1]^2 > 0

for i=0,...,6. Optional stronger source margins for those ordered pairs are

    (1016353,444291), (1150668,687760), (380276,104352),
    (242452,30000), (3486402,4967538), (424643,91575),
    (1071944,579814), all divided by 10^6.

Only positivity is part of the reference signatures. C07 proves the general
quadratic-kernel lemma with the exact equation H*v=0 and v[2] nonzero; positivity
of two minors alone is never taken as a PSD certificate for an arbitrary matrix.

## N04: triangle, cross terms and salience

The exact rational triangle is

    a0 = 125992104989487316477 / 10^20
    b0 = 158740105196819947475 / 10^20
    delta = 1/10000
    W = [[1,1,1],[a0+delta,a0,a0-delta],[b0,b0+delta,b0-delta]].

Let dx=(alpha-a0)/delta and dy=(alpha^2-b0)/delta. C09 checks the three
barycentric coordinates

    ((1+2dx-dy)/3, (1-dx+2dy)/3, (1-dx-dy)/3)

are positive, sum to one and map through W to (1,alpha,alpha squared).
Their stored cubic caches and all 21 derived rational generator columns are
also checked. A stronger optional barycentric margin is 33/100.

C10 covers exactly the 189 pairings g_ia-transpose*Q*g_jb with i<j and
a,b<3; the reversed orientation follows from symmetry. The optional common
strict lower margin is 17/1000.

C11 uses the fixed rational slice vector

    (-71246841,-101280383,-150296097,-110993458,
     -39802169,-119030527,-63286873) / 10^8

and proves all 21 rational dot products with generators positive. A stronger
optional margin is 999/1000. No interval computation is needed for these
purely rational inequalities. The subsequent no-line property is the literal
K intersect (-K)={0}; Mathlib's weaker ConvexCone.Pointed is not used.

## N05: universal obligations, not computations

C12 proves the entire real cone zero set. C15-C17 prove exact rational
Fourier–Motzkin projection and a finite rational halfspace representation,
including empty lists, zero coefficients, one-sided systems, zero dimensions
and zero generators. Those theorems may not be left as extra final premises.

C18-C21 prove an unrestricted-width Gram transport and trace obstruction.
C22 appends five zero rows and proves the actual real nonnegative factor.
C23 proves boundary membership in the symmetric subtype; C24-C25 discharge
all premises and refute the original assertion.

No 54,264-facet enumeration, 444-by-444 Gram expansion, full rank-three
certificate, repeated reverse cross check, or factor-width search is needed.
The formal witness may have a different finite order. This route does not
verify the source's additional order-444, cp-rank-seven or strict-positive-entry
claims, and those must not be advertised as formalized.
