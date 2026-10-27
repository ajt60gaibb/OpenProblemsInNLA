# TR-26 discriminant first-variation and isotropic multiplicity author evidence

Ten new sources are frozen and installed byte-identically in the assigned worktree. Exact source hashes and unique accepted compiler receipts are in AUTHOR_RESULTS.json. Accepted kernel logs, source text snapshots and failed diagnostics are retained alongside it. All accepted proofs use LeanCert kernel mode and only propext, Classical.choice and Quot.sound. Earlier thirteen frozen author modules remain unchanged.

- FixedDiscriminantAffine proves the exact full-degree normalization: FD(c) = (−1)^(k(k−1)/2) k^(k−2) discr(ofFn c), for k≥2.
- DiscriminantProduct derives the signed discriminant product identity from actual resultants and proves nonzero discriminant for a nonconstant separable polynomial.
- DoubleRootSplitVariation computes the actual FD derivative along ((X−r)^2+ε)S, with every nonzero scalar factor retained.
- FixedDiscriminantVariation defines the actual finite coefficient differential. It proves its vanishing along a genuine moving-double-root family, without inferring tangent membership from an unproved smoothness claim.
- OrdinaryDoubleRootVariation proves the derivative in every direction V of degree≤2+degree(S): doubleRootSplitScale(S) S(r)^3 V(r). This is nonzero when S is separable of positive degree and S(r),V(r) are nonzero. The positive-degree cofactor case covers every TR-26 target fixed degree 4d−2≥6. The degree-two constant-cofactor case is not claimed by this helper.
- CommonFactorWronskian proves the exact common-factor square identity and decomposes every actual simple denominator root with monic/separable cofactor.
- IsotropicWronskianWitness constructs an actual symmetric matrix with W=(X−r)^2S, separable full-degree S and S(r)≠0, by the proved finite-exception pencil.
- IsotropicTransverseWitness lifts numerator perturbation by 1 to an actual parameter line, giving a nonzero derivative of the original family determinant at each isotropic evaluation hyperplane.
- IsotropicMultiplicity proves that no evaluation factor square divides the family determinant, that no such factor divides any genuine complementary quotient, and IsRelPrime(E_iso,Q) for the literal equation F=E_iso*Q. It also exposes the generic square-factor/zero-line-derivative lemma for the nonisotropic route.

- MatrixReversal proves the exact original symmetric-coordinate involution, generic binary numerator and denominator reversal, the Wronskian orientation sign, and actual denominator/partial-double-root transport between charts.

This author evidence does not establish nonisotropic complementary-factor squarefreeness or the full Target. Independent non-author review, fresh closure replay, actual Linux CI and Comparator evidence remain campaign requirements. Two unused-simp warnings in DoubleRootSplitVariation and one informational ring-normalization hint in OrdinaryDoubleRootVariation are retained in their successful logs; they are not suppressed or presented as compiler failures.
