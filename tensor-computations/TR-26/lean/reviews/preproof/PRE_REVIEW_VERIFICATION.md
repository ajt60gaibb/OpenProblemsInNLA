# TR-26 independent exact pre-proof review

**APPROVE the frozen statement boundary and mathematical route for proof implementation. No statement correction is required.**

Reviewer: AI agent `/root/verification`, 2026-10-26. I did not author the contract, Challenge, manuscript, original statement, scaffold, or any TR-26 proof. This is a non-author pre-proof review. It proves no TR-26 endpoint and approves no later implementation, helper contract, Linux run, or Comparator result.

## Immutable inputs and fresh checks

This review binds immutable packet commit `94dd4adb910c5b5e1114528c1c4d9f272347743a` and the corresponding original review packet. The complete canonical problem, exact specification, actual live and Reviewed definitions, all three Challenge signatures, complete credited manuscript in Markdown and TeX, prior statement/source reviews, source provenance, and author preflight were read. Prior reviews and API inspections were context; they do not substitute for this assessment.

| Input | SHA-256 |
| --- | --- |
| INPUT_LOCK.json | 59314bd19a35f47dadd9a672517d4f9053682b4454b79c571cb915231342a91c |
| CONTRACT.md | 26625969b0c33b85d5e6dcb59dd2c3c9f9ca1389fcc92f4b3f1f1facb81d56a0 |
| Challenge.lean | 122ad60aaddf59e91dacd627637cf7237b8614d83b6d2eead381a76a698d7aba |
| Live TR26.lean | e0b38f44232ea35418e8afb9bcd0c1df0e2dd51642cda71e8bf62564a130095f |
| Reviewed/TR26.lean | e1700dde28c3679f126eaae1ea7cb16e979a18e94f1e77d198996f0f6ede6820 |
| Exact specification | 630e5dfb41a844e1105fc9af698520458449e1b58336b23d182e16d292114624 |
| Canonical README and ORIGINAL.md | 56f792c83ff7328f014eee02f89314b32ac6558adfae53753b4bfb87a15d9659 |
| Complete manuscript Markdown | 4a96398678689820dffd81522991fa4178062789afd657acc73194f0852185f8 |
| Complete manuscript TeX | bfb2f0fce6d67649dc8faca5965f79f898c4cb040645e721df5095446cd89b8e |

The independent input driver passes **53/53 checks**: all 24 frozen originals have exact locked hashes/lengths and equal both published trees `5487945e5a72abd952b0c89915915de8cc9b3e65` and `01ed3c64648d2d8350ba80c4018894b6d785d2c9`, their immutable packet copies, and the live inputs at the packet commit. All six additional contract/scaffold bindings match. All 217 registered ID/path pairs remain unchanged, including TR-26 at tensor-computations/TR-26/README.md.

A fresh private build directory, absent before this run, compiled Infrastructure, the live statement, Reviewed statement and Challenge, then proved the literal live/Reviewed Target equality by rfl. A separate file actually applied LeanCert kernel trust to all three Challenge placeholders: it exited one and rejected exactly three declarations through sorryAx. Thus elaborating the Challenge was not treated as a proof. The six compiler commands, exact generated control files, original logs and result are retained in verification/verification-preproof/.

The compiler is Lean 4.33.1, arm64 macOS, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. All ten dependency checkouts match the frozen manifest revisions and have clean tracked sources; Mathlib is 0df444a360eaa60ab8c11dca51a86af692955474 and LeanCert is 621a43d7cf21f87872392a01e874f2f1dbddc926. Only private TR-26 objects were written; existing pinned dependency objects were read. Statement logs show the three standard axioms. This is a boundary replay using the existing cache, not a dependency rebuild or a Linux receipt.

## Exact meaning of the endpoints

The two degree endpoints are exactly the two all-dimension conjuncts of Target, for every natural d with 2 ≤ d. The third theorem has the literal type NLA.Statements.TR26.Target. There is no genericity hypothesis, degree certificate, selected equation, assumed factorization, incidence oracle, or extra premise on these endpoints.

Upper-triangle coordinates represent every symmetric complex matrix without duplicate variables. The curve uses precisely the unweighted Veronese coordinates, all nonzero representatives, and both projective charts. The numerator and denominator are bilinear, with no conjugation. The ordinary partials have the correct zero-exponent cases. Testing both homogeneous parameter directions gives curve criticality, including at infinity; the radial derivative supplies no unintended extra stationarity condition.

VanishesOnOpen ranges over the entire actual polynomial vanishing ideal. Incidence is its common-zero closure on the nonzero curve and parameter cones. JacobianSpace spans all evaluated curve-variable partials of that ideal; its finite dimension gives the original generator-independent Jacobian rank. The bound is exactly d−1. Any convenient finite equation set must be proved to give the same local ideal and evaluated conormal span before it can replace this calculation.

IsotropicImage is the exact raw projection. NonisotropicClosure applies the separately required closure to the complementary projection. HasReducedDegree requires an actual nonzero squarefree homogeneous polynomial in the independent matrix variables, with an exact zero-set equivalence at every nonzero matrix. The requested degrees are positive, so nonzero homogeneity specifies the true reduced hypersurface degree. No irreducibility stronger than the literal Target is demanded.

## Mathematical route and exceptional cases

For m=2d, the numerator map is surjective: every coefficient uses a disjoint antidiagonal, with a nonzero coefficient one or two. A concrete tridiagonal right inverse also works. The denominator satisfies (t²−1)D=t^(m+2)−1; characteristic zero gives precisely m simple roots, excluding zero and infinity. The binary form (N_b D_a−N_a D_b)/m has fixed degree 2m−2 and affine value N'D−ND'. These normalization and sign identities agree with the actual quotient derivative.

At every parameter point, evaluation of this binary form is a nonzero linear functional of N. This supports the manuscript's hyperplane-bundle closure argument, including isotropic fibers. The rational normal curve contributes d−1 independent local normal gradients; the critical equation adds a rank exactly when its tangent derivative is nonzero. To discharge the actual Lean Ramification predicate, the proof must establish the full localized vanishing ideal and its conormal span, hold H fixed during z differentiation, and justify clearing local units and homogeneous radial directions. This remains a substantive proof obligation, rather than a new assumption.

At a simple denominator root r, F(r)=−D'(r)N(r). Under N(r)=0 the first-order term cancels and the root is automatically at least double. Hence the exact isotropic image is the union of the m distinct evaluation hyperplanes. Interpolation and numerator surjectivity show these forms are nonzero and pairwise nonassociated. Their product is a genuine squarefree homogeneous equation of degree m.

Off these roots, the first and second derivatives of N/D give two independent linear jet conditions. Their incidence has dimension m−1; only N=cD has identically zero Wronskian, and all other fibers are finite. This gives the nonisotropic image closure as a hypersurface distinct from every isotropic hyperplane. For m≥6, length-four and length-six interpolation bound the loci of a triple root or two double roots by m−2. The m=4 exception is handled separately: N=t³ yields F=t²(3+t²−t⁴), exactly one double nonisotropic root, four other simple roots, no isotropic root and no infinity root. The generic unique-double-root argument is therefore valid at d=2 as well.

The discriminant must be for binary forms of fixed degree k=2m−2, with projective roots and zero forms included. A specialized affine natDegree discriminant would not meet this requirement. The fixed discriminant is nonzero and homogeneous of degree 2k−2=4m−6. Its support is the nonisotropic closure together with the isotropic hyperplanes. At a generic unique-double-root point its differential is a nonzero scalar times evaluation of the perturbation at that root. Restricted to the numerator family this is nonzero by jets off D=0, and by −D'(r)δN(r) on each isotropic hyperplane. This supplies multiplicity one on every component before degree subtraction. Taking a radical while retaining an eliminant's degree would be insufficient. The resulting complementary degree is (4m−6)−m=3m−6=6(d−1).

Finally the proof must use the actual surjective affine numerator map and a linear splitting. Polynomial extension preserves the squarefree homogeneous equations and degrees, and products with the kernel commute with the required closure. Nonzero kernel matrices are present already at d=2; their numerator is zero, all curve points ramify, and both images contain them. The same applies to all numerators cD. A projective rational map alone would omit these parameters. The packet expressly retains these cases, both charts and infinity, rather than restricting to generic nonconstant quotients.

## Disposition

The locked route is sound for the exact published model and all requested d≥2. The full-ideal conormal bridge, fixed-degree discriminant specialization, dimension/interpolation arguments, multiplicity-one proof, exact zero sets and matrix pullback still require actual Lean proofs. This approval neither supplies them as hypotheses nor certifies unwritten helper definitions. Any later modified statement or material helper boundary needs separate review.

Preserve Matthew J. Colbrook's mathematical credit, all original sources and AI-assistance disclosures. This is independent AI-agent review, with no source-author participation or external human endorsement claimed. No canonical problem, original, registry, index, or other agent's branch was modified.

