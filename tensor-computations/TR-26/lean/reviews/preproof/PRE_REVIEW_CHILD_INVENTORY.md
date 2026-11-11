# TR-26 independent pre-proof statement and mathematics review

**Verdict: APPROVE the locked exact endpoints and mathematical route for proof implementation. No statement correction is required.** Reviewer: AI agent `/root/inventory/tr26_statement_audit`, 2026-10-26. I did not author or edit the statements, contract, scaffold, manuscript, or any TR-26 proof. This is one independent non-author review; it establishes no Lean proof, Linux receipt, Comparator result, or external human endorsement. Fresh boundary compilation belongs to the separate parent review and is not claimed here.

## Exact input binding

I read the complete credited manuscript in Markdown, checked its TeX source, and compared the canonical original, exact specification, live and Reviewed Lean definitions, contract, and all three Challenge signatures. I also consulted the retained prior review records and author preflight, without treating either as this independent approval.

| Input | SHA-256 |
| --- | --- |
| `INPUT_LOCK.json` | `59314bd19a35f47dadd9a672517d4f9053682b4454b79c571cb915231342a91c` |
| `Challenge.lean` | `122ad60aaddf59e91dacd627637cf7237b8614d83b6d2eead381a76a698d7aba` |
| `CONTRACT.md` | `26625969b0c33b85d5e6dcb59dd2c3c9f9ca1389fcc92f4b3f1f1facb81d56a0` |
| Live `NLA/Statements/TR26.lean` | `e0b38f44232ea35418e8afb9bcd0c1df0e2dd51642cda71e8bf62564a130095f` |
| Frozen `Reviewed/TR26.lean` | `e1700dde28c3679f126eaae1ea7cb16e979a18e94f1e77d198996f0f6ede6820` |
| Complete manuscript Markdown | `4a96398678689820dffd81522991fa4178062789afd657acc73194f0852185f8` |
| Complete manuscript TeX | `bfb2f0fce6d67649dc8faca5965f79f898c4cb040645e721df5095446cd89b8e` |
| Canonical README and exact `ORIGINAL.md` | `56f792c83ff7328f014eee02f89314b32ac6558adfae53753b4bfb87a15d9659` |
| Exact specification | `630e5dfb41a844e1105fc9af698520458449e1b58336b23d182e16d292114624` |

All 24 frozen original inputs match their lock hashes and byte lengths; all six additional contract/scaffold inputs match their lock hashes. Independently comparing every original through `git show` gives exact byte equality with both `5487945e5a72abd952b0c89915915de8cc9b3e65` and `01ed3c64648d2d8350ba80c4018894b6d785d2c9`. The live and Reviewed statement texts differ only in the frozen-file banner and namespace. The unchanged 217-entry registry retains `TR-26` at `tensor-computations/TR-26/README.md`. No canonical file, original, ID, status, or index was changed.

## Statement fidelity

`nonisotropic_degree` and `isotropic_degree` are exactly the two conjuncts of `Target`, separately quantified over every natural `d` with `2 ≤ d`; `target` has the literal closed type `NLA.Statements.TR26.Target`. No endpoint assumes genericity, an incidence certificate, a factorization, a chosen equation, or an unproved geometric bridge.

The actual upper-triangle coordinates represent every complex symmetric matrix without duplicate polynomial variables. The Veronese coordinates are unweighted and include both coordinate endpoints. Pairings are complex bilinear. The ordinary partials have correct zero-exponent behavior, and testing both parameter directions gives curve criticality, including at infinity and under nonzero representative scaling.

`VanishesOnOpen` ranges over the entire polynomial vanishing ideal. `Incidence` is its common-zero closure on the nonzero curve and matrix cones, and `JacobianSpace` spans all evaluated curve-variable partials from that ideal. This retains the canonical generator-independent rank threshold `≤ d-1`; replacing it by a convenient finite equation without proving equality of conormal spans would not discharge the endpoint. Products with coefficients have the same evaluated derivative span on the incidence, which explains the full-ideal interpretation.

`IsotropicImage` is the exact projection, with no added closure. `NonisotropicClosure` has the separately required Zariski closure. `HasReducedDegree` requires an actual nonzero squarefree homogeneous equation with an exact zero-set equivalence at every nonzero matrix. For the positive requested degrees, nonzero homogeneity gives the actual polynomial degree and a reduced projective hypersurface. The Target does not additionally demand irreducibility. No target weakening or conditional laundering was found.

## Mathematical route and exceptional cases

The manuscript's numerator surjection is genuine: disjoint antidiagonals supply every coefficient with nonzero factor one or two. For `m=2d`, `(t²-1)D=t^(m+2)-1` proves that the specific denominator has exactly `m` simple roots; zero and infinity are not roots. The binary Wronskian has fixed degree `2m-2`, and Euler's formula gives its affine value `N'D-ND'` with the stated sign and normalization.

The incidence proof must establish the full local ideal, then its evaluated conormal span, before identifying ramification with a multiple projective Wronskian root. The manuscript's smooth hyperplane-bundle argument and local normal equations support that bridge, including homogeneous radial directions and both charts. The contract correctly leaves its formal proof outstanding.

At a simple denominator root, `F=-D'N` and imposing `N=0` cancels the first-order Wronskian term. Thus the isotropic image is exactly the union of `2d` distinct evaluation hyperplanes, including exceptional matrix numerators. Off the denominator roots, the two critical-jet conditions are independent. The nonconstant-numerator fibers are finite, giving the source's hypersurface and separation arguments. Higher-order jet dimension bounds exclude triple roots and pairs of double roots for `d≥3`. At `d=2`, the explicit witness `N=t³` gives `F=t²(3+t²-t⁴)`: exactly one double root, four distinct other roots, no isotropic root, and no infinity root.

The discriminant must retain fixed binary degree `k=4d-2` under every specialization. A discriminant or resultant based only on the specialized affine `natDegree` would lose the required infinity behavior. The source instead uses degree `2k-2=8d-6` and proves nonvanishing from the proper discriminant support. Its unique-double-root differential is nonzero after restriction to the numerator family, both on the nonisotropic component and on each evaluation hyperplane. Consequently all factors occur once; subtracting the isotropic degree `2d` then gives the reduced complementary degree `6(d-1)`. Merely taking a radical and retaining the eliminant degree would be insufficient.

The source includes zero numerators, all numerators `cD`, and the nonzero matrix-to-numerator kernel, whose dimension is `d(d-1)/2` and is already positive at `d=2`. Working with the actual surjective affine map and its linear splitting preserves both sets, closure, squarefreeness, and degree at these parameters. No projective-map indeterminacy is silently removed.

The manuscript provides a sound route for the exact target. The conormal bridge, fixed-degree discriminant construction and specialization, multiplicity-one argument, exact zero-set equalities, and matrix pullback remain substantive formal proof obligations. This approval covers the locked inputs and signatures; it does not certify later helper definitions or implementations. Preserve Matthew J. Colbrook's mathematical credit and the recorded AI-assistance/review limitations.
