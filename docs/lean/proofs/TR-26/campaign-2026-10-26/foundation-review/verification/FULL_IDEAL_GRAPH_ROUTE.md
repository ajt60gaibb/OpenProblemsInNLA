# TR-26: independent assessment of the graph/conormal route

**The proposed route is mathematically sound for the exact d≥2 target, subject to proving the concrete lemmas below.** Reviewer: non-author AI agent /root/verification, 2026-10-26. This is a read-only route assessment beside the six-module review of 2a2d1815, not a proof, new helper-contract approval, endpoint approval or Linux claim.

On the first curve chart write z=c(1,t,…,t^d), with c≠0, and let W(t,H) be the actual universal chart Wronskian, linear in the independent symmetric-matrix coordinates. Fix H₀≠0 and t₀ with W(t₀,H₀)=0. Suppose an actual coefficient A_j(t₀)≠0. On a neighborhood where A_j is nonzero, set

    H(t)=H₀−[W(t,H₀)/A_j(t)] e_j.

Linearity gives W(t,H(t))=0 and H(t₀)=H₀. The map is holomorphic there. H(t) stays nonzero after shrinking the neighborhood: use any coordinate nonzero at H₀, not necessarily j. The actual nonzero polynomial D has finitely many zeros; away from them the graph, with this fixed nonzero c, is OpenCritical. This needs the exact local-Wronskian/quotient-derivative comparison, including the second homogeneous parameter direction by Euler's identity.

Every polynomial f in the actual full vanishing ideal therefore vanishes on a dense subset of this neighborhood. Continuity makes f(c v(t),H(t)) identically zero on the whole neighborhood, including an isotropic t₀. This proves **W=0 implies the original Incidence**, for every polynomial of its full ideal; it does not merely prove membership in a chosen equation set.

At the base point,

    H′(t₀)=−[W_t(t₀,H₀)/A_j(t₀)] e_j.

Thus W_t=0 makes the entire parameter derivative zero. The complex chain rule now gives Σ_i (∂f/∂z_i) c v′_i(t₀)=0. The parameter-gradient terms really vanish; holding H fixed without this derivative calculation would be insufficient.

For the radial tangent, apply the same established incidence statement to λc for every λ near 1, keeping H₀ fixed. This remains valid when D(t₀)=0; a scaling curve alone must not be asserted to be OpenCritical there. Differentiation gives Σ_i (∂f/∂z_i) z_i=0. Equivalently one can prove scaling invariance of the full incidence from that of OpenCritical. Radial and chart tangents are independent: their first two coordinates are (c,ct₀) and (0,c). Use **complex-bilinear coordinate annihilators**, not Hermitian orthogonality. Their common annihilator has dimension (d+1)−2=d−1, giving the full Jacobian-space upper bound after taking its span.

A simple global polynomial supplies the converse and lower bound. Choose any fixed positive K bounding the degree in t of the **universal** Wronskian, and write W(t,H)=Σ_{l=0}^K w_l(H)t^l, with polynomial (indeed linear) coefficients in H. A coarse positive bound is sufficient; this witness need not establish the final fixed binary discriminant degree. Put

    G(z,H)=Σ_{l=0}^K w_l(H) z₁^l z₀^(K−l).

It belongs to the actual full vanishing ideal. On the first chart it equals c^K W. At the only omitted curve point, d≥2 implies z₀=z₁=0, so positive homogeneity makes G=0 as well. This is a global vanishing argument; coefficients obtained by freezing H₀ would not suffice. Consequently Incidence implies W=0, and at such a point the curve-tangent derivative of G is c^K W_t.

For i=2,…,d the global curve equations

    P_i=z_i z₀^(i−1)−z₁^i

also lie in the full vanishing ideal. On z₀=c≠0 their gradients are independent, since coordinates 2,…,d form the diagonal c^(i−1). They annihilate the radial and chart tangents. If W_t≠0, the gradient of G does not annihilate the chart tangent, so it adds a d-th independent vector. This contradicts rank≤d−1. When W_t=0 the upper bound and these normals give rank exactly d−1. No equality with a proposed localized generating ideal is needed for this argument.

The reversed chart uses z_d,z_(d−1) and reversed normal equations. Verify its exact Wronskian sign: the same homogeneous binary W evaluated at (u,1) is the negative of the affine quotient Wronskian N′D−ND′ in u. This nonzero constant sign changes neither zero nor derivative-zero conditions, but must be tracked in the formal identities.

The only essential coefficient-selection obligation is to prove some A_j(t₀)≠0 at **every** chart point for the actual model. At D≠0 use genuine numerator first-jet surjectivity; at a simple D-root use W=−D′N and nonzero evaluation. Both must follow from actual numerator coordinates and the simple-root theorem, rather than enter the final result as genericity assumptions.

No exceptional parameter is lost. H=0 and c=0 are correctly excluded by the original projective definition. Nonzero matrix-kernel elements and N=cD are included: W(t,H₀) is identically zero, so the graph is constant in H and the same argument applies. Isotropic roots are covered by density; infinity is covered by the reversed chart; the explicit normals remain independent at d=2. Arbitrary, nonhomogeneous full-ideal polynomials are covered by the graph and chain-rule argument, so no hidden assumption that every ideal element itself is homogeneous is needed.

**Disposition:** this is a faithful replacement for a substantially heavier local-ideal proof of the incidence/rank bridge. It still requires the actual chart identities, degree bound for the global witness, coefficient-selection lemma, dense-omission/differentiation arguments and bilinear finite-dimensional rank calculation in Lean. It supplies no discriminant converse, multiplicity-one factorization, reduced degree formula or full Target proof.

