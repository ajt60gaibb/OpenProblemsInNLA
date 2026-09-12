# MI-23 independent final proof review — referee 2

**PASS for all eight frozen exports and the complete canonical conjecture
negation.** No mathematical or Lean correction is requested. Actual Linux
Comparator/default-kernel execution and the other independent final referee
remain separate release gates.

Reviewer: coordinating agent `/root`, independent of implementer
`/root/formal_review_standards`, 12 September 2026. I reviewed the original
statement boundary before implementation and have now read every completed
mathematical module and public export, the full retained source proof and
canonical statement. I separately rebuilt the proof and inspected its actual
dependencies. No mathematical candidate files were changed by this review.
This is AI-agent review applying relevant Tau Ceti criteria, not human peer
review, Tau Ceti endorsement or endorsement by the mathematical source author.

Mathematical counterexample: Matthew J. Colbrook, Department of Applied
Mathematics and Theoretical Physics, University of Cambridge. Formalization:
George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA, with substantial
AI-agent assistance. The Mathlib and LeanCert authors retain their own credit.

## Version and exact statement boundary

The proof freeze `reviews/proof-freeze.json` has SHA-256
`18fbf9a74e6006ca2b4159be62730c6df4faf38d472250b8ca1e7e54bf392ecb`.
All 25 bound inputs were rehashed unchanged. The three original mathematical
sources were independently compared with their earlier reviewed hashes and
immutable upstream revision `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`.

| Boundary | SHA-256 |
| --- | --- |
| Definitions | `1ca2386528fc7ff944f84088842f62c5f33a38f14cde7ee8127972be29696def` |
| Challenge | `283bca1ced50d7953f9946629c24e99f944d81095f9c822fbb3b58a44e01e189` |
| Numerical targets | `2f8e41d440d3e24732a1c2b70c0710ad0d88367c2aac7979141959a8d8df25ee` |
| FunctionalCalculus | `5603fb214d01f327ba297af151e278ed8f8310368272c59180dd52ebd87839a1` |
| SpectralNorm | `af43452f42fde8c361d3ab21c4bcf9839f355b7c06f905dbc56c1eb591c6c5a3` |
| NormBounds | `1fd4f9d91818470bfee7e3bb164baaaf120b80ee088ff827134be0e2ac867ad3` |
| Witness | `4d7d79b742e614712d5ecc052c04df135cde6b6548ec7cb19f6cfbae0ef987b7` |
| Arithmetic | `d5895f0636fa3aa3887721c610ee9f526cc35a6838e1d4ad7e7ba7f0548af3d9` |
| Proof | `a82ba18b834453491e4d7bb50de23c08555b92bb70e573551d11e714a404984a` |
| Solution | `575f2fd27922d2725d93ada823bfeb4da70407d7fd9c31fb7cf1753a5fdbd243` |

Both statement approvals were recorded before implementation. The complete
Definitions, Challenge and numerical targets remain identical to that approved
boundary. The subsequent README update and default Lake target change from
Challenge to Solution are documented packaging changes; dependencies and
Comparator configuration are unchanged. All eight public signatures agree with
the frozen Challenge after whitespace normalization. Comparator's selected names
also agree with the independent earlier statement audit, with no definition
exceptions and only the three permitted axioms.

## Full target and analytic bridges

The conjecture retains all positive dimensions, complex positive definite A and
B, arbitrary real p ≥ 1 and t in [0,1], and both original parameter regions
r,s ≥ 1 or r,s ≤ 0. Real powers are genuine CFC powers, and the generalized mean
has the exact original noncommuting factor order. `LogMajorized` retains equal
length, every proper nonempty prefix-product inequality, and equality of full
products. It is not replaced by a norm inequality or weak log-majorization.

`FunctionalCalculus.lean` discharges strict positivity of arbitrary real powers
and all generalized means. For positive definite X,Y it constructs the actual
positive square root R and inverse Rinv of Y, proves both inverse identities,
and identifies R(XY)Rinv with the positive definite sandwich RXR. The actual
characteristic polynomials agree. Using the Hermitian spectral theorem, the
proof transfers the full complex root multiset, including multiplicities, to
the sorted real list and proves length n, positivity, descending order and
the complete determinant product. Thus taking real parts in the definition
does not discard imaginary information on any matrix class in the conjecture.

`SpectralNorm.lean` proves that the actual first characteristic-root eigenvalue
of a positive definite matrix equals its Euclidean operator norm. The zero
default in `getD` is excluded by the proved positive dimension and list length.
Unitary diagonalization is applied with the L2 operator norm; I inspected the
actual Mathlib spectral, diagonal norm and Gram norm lemmas and their Euclidean
linear-map definitions. No default entrywise matrix norm is substituted by a
typeclass accident. The conjugate-transpose Gram identity then proves
largestEigenvalue(X²Y²) = operatorNorm(XY)² for every positive dimension and
positive definite X,Y, with the correct product orientation.

`NormBounds.lean` proves the entry lower bound by evaluating the genuine
Euclidean map on a coordinate unit vector. Its upper bound uses the actual
positive semidefinite Gram matrix, whose norm is bounded by its trace, and
identifies that trace with the sum over every squared complex entry modulus.
These are generic complex-matrix theorems, not inequalities assumed of the
witness or an auxiliary norm defined to make the comparison true.

## Exact witness and contradiction

The source's D, T, A = D² and B = DT⁸D are unchanged. An exact rational LDL
factorization proves T positive definite using pivots 2,49/2,150/49 and an
invertible triangular factor. This is a valid alternative to the source's
principal-minor test. All witness positivity, both diagonal inverse identities,
and the real-power composition hypotheses are discharged in Lean.

The true normalized inner matrix is T⁸. Actual CFC composition identifies its
1/8 and 7/8 powers with T and T⁷; the generalized means are therefore the
actual G = DTD and H = DT⁷D. These rational matrices do not replace the means
by definition or enter as unproved equalities.

The checked addition chain computes T²,T⁴,T⁷,T⁸ with exact integer/rational
matrix identities. Every private certificate is proved by kernel arithmetic
and is retained transitively. The selected complex entry and full Frobenius
sum agree with my earlier independent exact reconstruction and the source:
1260589125202/9 and 2009446159144992718181231562721/107495424, respectively.
Their squared separation is exactly
99434824489435745411095588895/107495424 > 0. Approximate eigenvalues and the
source's unnecessary intermediate decimal thresholds are avoided.

The actual LeanCert proof of this single rational inequality uses
`verify_strict_upper_bound_dyadic_checked`, the constant-zero expression on
the singleton box [0,0], precision −53 and depth 10. I inspected its emitted
proof and checked its retention through `squaredGap_positive`, the strict norm
comparison, strict largest-eigenvalue comparison, failure of log-majorization,
and the final universal-conjecture negation. It is not an unused certificate
beside a separate unverified numerical assumption.

At n = 3, r = s = 1, p = 2, t = 1/8, every original admissibility condition
is established. Both ordered lists have actual length three. The first prefix
is therefore a proper prefix and equals the actual largest eigenvalue on each
side. Its strict reverse inequality refutes the full log-majorization relation,
including the relation whose definition still retains the full-product
equality. The final proof instantiates and negates the full canonical target.
It does not claim every parameter choice fails or contradict the known narrower
t interval. No broader semidefinite or unrelated singular-value conjecture is
silently substituted for the retained positive-definite problem.

## Fresh validation and evidence

I freshly elaborated Definitions and all seven implementation/export modules
in dependency order into a separate output prefix. All eight commands returned
zero without warnings; fresh project artifacts take precedence over existing
ones. All ten dependency sources are clean at their exact manifest pins. This
macOS arm64 build reuses pinned library artifacts and is not represented as
Linux execution or a complete library-source rebuild.

All 64 explicit kernel trust checks and printed transitive axiom reports passed
with exactly `propext`, `Classical.choice`, `Quot.sound`. The implementation
contains no holes, custom axioms, unsafe/native shortcuts, environment mutation,
or import of Challenge. My separate inspection traversed 172 actual project
declarations, including private arithmetic certificates, and required 23
substantive mathematical/certificate dependencies. All were present. Three
additional kernel checks on the point certificate and final contradictions
passed. Source scanning supplements these actual proof and axiom checks.

[Independent evidence](proof-referee-2-root-evidence/manifest.json) has SHA-256
`ac26cd126de1e236bb85549a5d9994c09b8b92d021e9f2de102764cae1180816` and binds
the fresh driver, exact commands and logs, source/signature checks, clean pins,
separate dependency inspection and read-library hashes. The inspection log
SHA-256 is `1a8fb1c06b4c9f5c6383c82320487c8e01d27b983f3558087cece753ef37f38d`.
I read its substantive dependency, definition and certificate output, including
the private power-certificate links; repeated generated arithmetic auxiliaries
are covered by the recorded traversal and kernel checks.

This review approves the completed proof at the exact frozen boundary. Actual
Linux Comparator/default-kernel acceptance, negative controls, independent
operational audit and truthful publication metadata remain required before
canonical promotion. No canonical status, ID, commit, push or PR changed here.
