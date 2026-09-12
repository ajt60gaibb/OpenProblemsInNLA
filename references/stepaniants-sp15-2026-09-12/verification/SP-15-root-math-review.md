# SP-15 coordinating mathematical audit

Reviewer: coordinating Codex agent `/root`. Date: 12 September 2026 UTC.
Verdict: **PASS for a complete negative answer to the original SP-15 question**. This is an informal AI-agent audit, not formal verification or external human peer review. A separately assigned independent agent must still audit the candidate before publication.

## Frozen material and target

I read all of `/tmp/nla-fresh-round5/sp15/RESULT.md`, 9,440 bytes, SHA-256 `d992da0546924d7fbc9f1bb0e89e00b1442ec3c3045c739722c9767078ce40c1`. I compared the conclusion with the retained canonical SP-15 README at upstream base `1f22006bdaa4659fcaa0bb775a887685cd3cc566`. A single dimension N=9 with an infinite family in one complete shifted-singular-value data fiber, all in distinct unitary classes, refutes its universal finite bound. An exceptional fiber is permitted; generic finiteness does not settle the question.

I directly opened Ransford's primary 2010 paper, https://www.impan.pl/shop/en/publication/transaction/download/product/86371 . Theorem 5.4 on printed page 336 permits a closed exceptional set, and the ensuing discussion on printed page 337 asks whether that set can be empty. There is no simple-spectrum, nonderogatory, diagonalizable, or invertibility restriction. Nilpotent matrices of fixed Jordan type are eligible. The note correctly distinguishes unitary similarity from ordinary similarity and preserves the original authors' attribution.

## Independent re-derivation

For A with blocks X=P^(1/2), Y=Q^(1/2) on its first superdiagonal, I multiplied (A-zI)*(A-zI). Its diagonal blocks are |z|^2 I, |z|^2 I+P, and |z|^2 I+Y*Y. The off-diagonal blocks are -conj(z)X and -conj(z)Y with the appropriate adjoints. For t>0 and s=t+|z|^2, the first Schur complement gives K/s, K=s^2 I+tP. Eliminating it and using det(sI+BC)=det(sI+CB) gives

det[tI+(A-zI)*(A-zI)] = det[s^3 I+st(P+Q)+tPQ].

The order PQ is correct. Left multiplication by K, not an illicit commuting rearrangement, gives the final expression. Positivity of P ensures every inverse used exists for t>0. Equality for all t>0 extends as a polynomial identity in t for each fixed z, so equality of F(u,s)=det[uI+s(P+Q)+PQ] determines every shifted singular value with multiplicity. The proof needs only this implication, not injectivity of the change of variables.

I independently counted the invariant coefficients. F has total degree at most r in the independent scalars u,s, since each matrix entry is affine in those scalars. For real u,s its matrix is (P+sI)(Q+sI)+(u-s^2)I. Adjoint reverses the two Hermitian factors, and the determinant of BC+cI equals that of CB+cI. Hence F is real on R^2 and every coefficient is real. At r=3 there are ten monomials of total degree <=3; the u^3 coefficient is identically one. Thus at most nine varying real coefficients suffice. Positive definiteness does not introduce extra coefficient coordinates.

The proposed parameter domain has dimension ten: three ordered positive eigenvalues of P, three real diagonal entries of Q, two positive real entries q12 and q13, and one unrestricted complex entry q23. Its positivity conditions define a nonempty open subset of R10, as verified by the displayed diagonally dominant example.

To test whether the dimension count overcounts unitary classes, I checked every possible intertwiner of the full matrix. Invertibility of X,Y gives the same coordinate flag ker A subset ker A^2 for every parameter. A unitary intertwiner preserves that flag and its orthogonal differences, hence is block diagonal. Its middle block simultaneously unitarily conjugates P and Q. Ordered distinct diagonal entries force identical P and a diagonal middle unitary. The two positive real entries q12,q13 force both relative phases to be one. This middle unitary is scalar, and Q must be identical. No block permutation, adjoint, transpose, or reversal is an additional unitary equivalence: preservation of the ordered kernel flag rules these out. Thus distinct parameter points really are distinct unitary classes.

The coefficient map is a real polynomial map on an open subset of R10 into R9. An attained maximal derivative rank k exists because possible ranks form a finite set. A nonzero maximal minor persists on a neighborhood; maximality bounds the rank above, giving constant rank there. The k=0 case is also covered. The constant-rank theorem gives a local fiber of dimension 10-k >=1 and an injective smooth curve. All its points stay in the open positive domain. Smoothness of positive definite square roots makes the resulting matrix curve smooth; the gauge argument makes it injective even after passage to unitary classes.

Finally A^3=0 and A^2 has invertible block XY, so the kernel dimensions are 3,6,9 and all members have Jordan type (3,3,3). Taking arbitrarily large finite subsets of the curve defeats every finite M9. No explicitly numerical fiber is required for an existence counterexample. The argument uses the standard constant-rank theorem, not an unverified generic-rank computation; supplementary finite determinant diagnostics are not the proof.

I found no substantive gap and request no mathematical amendment to the frozen candidate. The external generic finiteness theorem remains compatible with this exceptional family. Publication conversion, current eligibility, attribution, independent review, and PDF layout remain separate gates.
