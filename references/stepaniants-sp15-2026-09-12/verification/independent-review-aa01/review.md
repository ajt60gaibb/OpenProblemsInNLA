# SP-15 independent full-proof review

**Verdict: PASS for the complete negative resolution of the original SP-15 target.** The frozen proof establishes a single shifted-singular-value fiber containing a smooth curve of pairwise unitarily inequivalent complex matrices of order nine. This disproves the requested finite bound at order nine, and therefore the assertion for every order. No mathematical correction is required.

**Reviewer:** separate Codex agent `/root/review_aa01`. The complete proof and exact canonical target were read, and every substantive step was independently reconstructed before this verdict. The coordinating agent's review was not read or used. The author's diagnostic checker was not read, imported or run for this audit. This is an informal automated-agent review, not external human peer review, a formal proof-assistant certificate, or a priority determination.

**Exact reviewed source:** [RESULT.md](../RESULT.md), 9,440 bytes, SHA-256 `d992da0546924d7fbc9f1bb0e89e00b1442ec3c3045c739722c9767078ce40c1`. The [canonical target snapshot](../canonical-statement.md) has 3,781 bytes, SHA-256 `75fba96fcb660f6420f315db19df6e8c0d3ccf0a858ceb2cf587096f6343eac3`. Its contents were also read directly from the canonical repository path at the published base. Neither source was edited in this review.

## 1. Target and primary-source comparison

The retained question asks for a finite bound depending only on the complex matrix order, valid for every fiber of the complete data consisting of all singular values of every complex scalar shift. It has no genericity, simple-spectrum, nonderogatory, or invertibility assumption. A single infinite fiber at order nine is therefore sufficient to refute the whole quantified assertion.

I directly downloaded the published [Ransford 2010 primary paper](https://www.impan.pl/shop/en/publication/transaction/download/product/86371), DOI [10.4064/bc91-0-19](https://doi.org/10.4064/bc91-0-19), and read and visually inspected Definition 3.1 on printed page 331, Theorem 5.4 on page 336, and the exceptional-set discussion on page 337. They give exactly the data definition, finiteness outside a closed measure-zero exception, and the question of removing that exception. The independent author-manuscript web extraction agrees. The published PDF is 425,024 bytes with SHA-256 `acce0807dd00ca47bca068f0437bc0e60209ba7af482be02ac7306bd5c23b4e0`; it and the inspection images remain private.

The indexed primary text of Fortier Bourque and Ransford's [2009 article](https://doi.org/10.1112/jlms/jdn085), Section 6.2, asks the same empty-exceptional-set question. Direct retrieval of its full author manuscript failed, so I do not claim a complete independent inspection of that PDF. The complete published 2010 primary restatement supplies the exact scope needed here. No result from either source is a premise of the new matrix construction. The original theorem and question retain their authors' attribution.

## 2. Block multiplication and the Schur identity

Let $X=P^{1/2}$ and $Y=Q^{1/2}$ be positive definite Hermitian roots, and let $A$ have the two successive superdiagonal blocks $X,Y$. I independently multiplied $(A-zI)^*(A-zI)$ by columns. The first diagonal block is $|z|^2I$, the second is $|z|^2I+X^*X$, and the third is $|z|^2I+Y^*Y$. The only nonzero off-diagonal blocks are $-\overline zX$, $-\overline zY$ and their adjoints. This agrees with the source; in particular the conjugations and block orientations are correct.

For $t>0$, put $s=t+|z|^2$. The first Schur complement has middle block

$$sI+P-|z|^2P/s=(s^2I+tP)/s=K/s.$$

Both eliminated blocks are invertible because $s>0$ and $K>0$. The first determinant factor $s^r$ and the denominator in $\det(K/s)$ cancel exactly. The remaining factor is

$$\det K\,\det\bigl(sI+Y^*(I-|z|^2sK^{-1})Y\bigr).$$

Cyclic determinant invariance replaces $Y^*BY$ with $BYY^*=BQ$, where $B=I-|z|^2sK^{-1}$. Multiplying the last determinant on the left by $K$ yields

$$\det\bigl(sK+(K-|z|^2sI)Q\bigr).$$

Since $K=s^2I+tP$ and $s-|z|^2=t$, this is exactly

$$\det\bigl(s^3I+st(P+Q)+tPQ\bigr).$$

The product is $PQ$ in this order. No step moves $Q$ through $K$ or presumes that the positive definite matrices commute. The calculation is valid in every block order, and includes $z=0$.

Factoring $t$ from each of the $r$ rows gives the displayed $t^rF(s^3/t,s)$. For each fixed complex $z$, equality of $F$ makes the two Gram determinant polynomials agree for all real $t>0$. Polynomial identity then gives the entire characteristic polynomial, including every root and its multiplicity. Its roots are precisely the negatives of the squared singular values. This recovers all sorted singular values for all shifts, including zero singular values; the argument needs neither $t=0$ in a Schur complement nor an inverse of $A-zI$.

Only the implication from equal coefficient data to equal shifted singular values is needed. It does not matter whether this polynomial data contains redundancy or whether the converse implication holds.

## 3. Nine real coefficient slots

Each entry of $uI+s(P+Q)+PQ$ is affine in the two formal variables $u,s$. Its determinant therefore has total degree at most $r$. The coefficient of $u^r$ is one.

For real $u,s$, rewrite this matrix as $(P+sI)(Q+sI)+(u-s^2)I$. Conjugate transpose reverses the two Hermitian factors. The determinant identity $\det(BC+cI)=\det(CB+cI)$, valid also when either factor is singular, equates the two determinants. Thus $F(u,s)$ is real for every real pair $(u,s)$. The imaginary part is a real polynomial vanishing on the whole plane and is identically zero. All coefficients of $F$ are real, even when $P,Q$ do not commute and $Q$ has nonzero imaginary entries.

At $r=3$ there are ten monomials of total degree at most three, including the fixed $u^3$ term. Hence nine real coordinates determine $F$. Their values may satisfy additional relations; that could only lower the coefficient-map rank and strengthen the dimension argument. Dependence of the coefficients on the ten matrix parameters is polynomial, since the roots $X,Y$ do not occur in $F$.

I also derived a separate explicit check on the chosen gauge slice. Put

$$L_i=u+s(p_i+q_i)+p_iq_i.$$

Direct expansion of the three-by-three determinant gives

$$\begin{aligned}
F={}&L_1L_2L_3-L_1(s+p_2)(s+p_3)(c^2+d^2)\\
&-L_2(s+p_1)(s+p_3)b^2-L_3(s+p_1)(s+p_2)a^2\\
&+2abc(s+p_1)(s+p_2)(s+p_3).
\end{aligned}$$

The two oriented cycles contribute conjugate factors $ab(c+id)$ and $ab(c-id)$, which explains their real sum. The reviewer-written [coefficient checker](coefficient_check.py) expands the determinant independently by all six permutations over a Gaussian-integer polynomial ring in twelve variables. Its [exact output](coefficient-check.json) verifies this identity, real coefficients, all ten permitted $(u,s)$ slots, and the fixed leading coefficient. The expansion has 136 parameter monomials. This is a universal symbolic check on the ten-parameter family, not a finite floating-point sample. It does not formally certify the Schur or differential-topological parts of the proof.

## 4. A genuine ten-dimensional family of distinct unitary classes

The parameter count is exactly ten: three distinct ordered positive entries of $P$, three real diagonal entries of $Q$, two positive real entries $a,b$, and the real and imaginary parts $c,d$ of its final off-diagonal entry. These parameters specify different Hermitian pairs. Positive definiteness, the ordering, and positivity of $a,b$ define an open subset of $\mathbb R^{10}$. It is nonempty: the example with $P=\operatorname{diag}(1,2,3)$ and $Q$ having diagonal four and off-diagonal one has eigenvalues six, three and three.

Invertibility of $X,Y$ gives exactly the common coordinate flags

$$\ker A=\mathbb C^3\oplus0\oplus0,
\qquad\ker A^2=\mathbb C^3\oplus\mathbb C^3\oplus0.$$

Any unitary intertwining two members must preserve both flags. It therefore preserves their three orthogonal successive summands and is block diagonal. This proves the claimed restriction for every possible full $9\times9$ unitary; it is not a restriction to a preferred subgroup of intertwiners.

The two block equations give $P'=U_2^*PU_2$ from $X'^*X'$, and $Q'=U_2^*QU_2$ from $Y'Y'^*$. The two uses of the middle unitary are consistent. The strict ordering and equal spectra force $P'=P$ entry by entry; simple spectrum then forces $U_2$ to be diagonal unitary. Positivity of both $Q_{12}$ and $Q_{13}$ on both sides forces both relative phases to be one, including equality of their magnitudes. Thus $U_2$ is scalar and $Q'=Q$.

Consequently the entire ten-parameter slice is injective modulo unitary similarity. There is no unremoved continuous stabilizer, permutation freedom, block interchange, or special treatment of a real $Q_{23}$. Complex conjugation is not an extra allowed unitary operation. Equal Jordan type does not imply unitary similarity and does not invalidate this argument.

## 5. The constant-rank argument gives one fixed infinite fiber

The smooth polynomial map $\Phi:\Omega\to\mathbb R^9$ has derivative rank at most nine. The set of actually attained ranks is a nonempty finite set of integers, so it has an attained maximum $k$. This step does not require compactness of $\Omega$ or a priori knowledge of a point where the rank is nine.

If $k>0$, a nonzero $k$-minor at a maximizing point remains nonzero on a sufficiently small open neighborhood. The rank is at least $k$ there and cannot exceed the global attained maximum. If $k=0$, it is already zero on every such neighborhood. In either case there is a nonempty constant-rank neighborhood entirely inside the positive definite parameter domain.

The smooth constant-rank theorem now identifies the fiber through that actual point with a local submanifold of dimension $10-k\ge1$. Choosing one coordinate line in this local fiber gives an injective smooth curve on an open interval. This is a curve in a single fixed coefficient fiber, not a collection of unrelated fibers of growing cardinalities. No properness, generic finiteness, algebraic-dimension heuristic, or numerical Jacobian rank is assumed.

The positive definite square-root map is smooth. For example, its derivative is obtained by solving the Sylvester equation $XH+HX=K$; positive eigenvalues make the linear map invertible. Composing the parameter curve with the root construction gives the smooth matrix family. The unitary gauge proof makes all distinct curve points inequivalent. Thus every finite proposed bound is defeated by taking sufficiently many distinct points on this one curve. An explicit numerical value of its fixed coefficient tuple is not required for this existential counterexample to a universally quantified finiteness assertion.

Finally, $A^3=0$ and the sole nonzero block of $A^2$ is the invertible $XY$, so the index is exactly three. The successive kernel dimensions $3,6,9$ yield precisely three Jordan blocks of size three. This verifies the theorem's ancillary claim and explains compatibility with known ordinary-similarity conclusions.

## 6. Verdict and boundaries

The full canonical SP-15 assertion is refuted at order nine. The proof supplies more than the negation of a uniform bound: one exceptional fiber already contains uncountably many unitary classes. It leaves the generic finiteness theorem intact, makes no claim that nine is the smallest possible order, and does not replace unitary similarity by ordinary similarity or omit any shifted singular value.

The complete frozen proof passes this independent mathematical audit without an amendment. The positive verdict does not depend on the author's finite checker, a literature-search conclusion, the coordinating review, or the new checker's output alone. Publication eligibility and exact source/PDF conversion remain separate checks.

Signed: `/root/review_aa01`, independent Codex-agent reviewer, 12 September 2026 UTC.
