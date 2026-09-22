# TR-27 ProjectiveGeometry independent module review

Reviewer: `/root`, Codex AI agent, 2026-09-22. Author: `/root/infrastructure_audit`. I did not implement ProjectiveGeometry, but authored its Semantics dependency; this report independently reviews the new geometry module and does not independently review my own dependency or a complete TR-27 package.

Verdict: **APPROVE** exact frozen `admissible_geometry` and its supporting arguments. No complete counterexample, human peer review or publication approval is claimed.

I read every proof. Closedness uses every homogeneous component of every polynomial in the actual homogeneous ideal, and recombines their finite sum to obtain membership in the entire zero locus. The converse is closure extensivity. This does not infer closedness merely from a chosen parametrization.

The homogeneous-vanishing bridge covers each nonzero cone vector via its actual projective representative and cancels only a nonzero scalar power. At the zero vector it uses an existing nonzero cone point and evaluation at scalar zero, so degree-zero equations are included without assuming positive degree. Coordinate surjectivity transports this statement to every point of the ordinary complex affine zero locus. The complex Nullstellensatz and primality then identify its vanishing ideal with the original radical prime ideal.

For irreducibility, the proof assumes the full point set is covered by two closed sets but is contained in neither, chooses one point outside each, and extracts the corresponding homogeneous separating equations from the exact closure definition. Their homogeneous product vanishes at all covered points, so the preceding bridge puts it in the prime ideal. Primality forces one factor to vanish at the corresponding separating witness, a contradiction. Nonemptiness is constructed from the admissibility witness. These are actual complex projective points and actual closed-set unions, not a prime-spectrum surrogate.

Full projective span is proved by placing every cone vector in the linear span of projective representatives, treating zero separately, and then using the assumed full cone span. The result includes all three required geometric claims with the exact frozen hypotheses and no rank premise. The reduced-coordinate-ring assumption is preserved by the signature even though this point-set argument only needs the prime ideal and other displayed conditions.

I rebuilt Definitions, Semantics and ProjectiveGeometry in a fresh external directory. All exited zero without warnings; the new export's transitive closure is exactly `propext`, `Classical.choice`, `Quot.sound`. No Challenge import, placeholder, native proof or custom axiom is present. This is cached development verification, not a Linux Comparator run. Attribution and affiliation remain intact without contact email.

## Reviewed byte binding

- `NLA/TR27/ProjectiveGeometry.lean`: `6003e71fe3beb48a768c62cff8199f39eefe05d29f0e6123195a763e9a9bf8bb`
- `NLA/TR27/Semantics.lean`: `d1a2e30e0cec093d276c529268d8744e5c53b04706499b58827c435cf460142c`
- `NLA/TR27/Definitions.lean`: `5f9cbf71a854a8a8a968ea4713c12bf501726e294ed7cccacff390dafb687056`
- `Challenge.lean`: `158b0f5d8eb23a3165caecf7ceed5c3f6ab87310c0576bbe9f57cbe3cfbe0ee5`
- `reviews/root-projective-geometry-typecheck.log`: `7ea13a4fb979ced009ab2def4b3d6f7bb24a94fe51510707059dd0a0906e2490`
