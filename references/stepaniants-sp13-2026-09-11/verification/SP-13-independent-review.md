# Independent mathematical review: SP-13

**Reviewer:** independent Codex agent `/root/review_md03_md04`  
**Review date:** 12 September 2026 UTC  
**Verdict:** **PASS for the complete canonical mathematical target**, using the explicitly cited published weak-type theorem. No mathematical correction is required in the reviewed version.

This reviewer did not author the candidate. The review comprised a fresh reading of the exact canonical statement, the entire frozen candidate, direct inspection of the primary theorem and its normalization, and an independent reconstruction of every finite-dimensional estimate and limiting argument. This is an independent AI-agent review, not external human peer review or formal verification. The verdict concerns mathematical correctness of the candidate; it is not a claim of novelty, repository acceptance, publication, or an independent full public-network audit.

## Exact source bound to this review

- Candidate: `/tmp/nla-fresh-round5/sp13/RESULT.md`.
- Bytes: **11,248**.
- SHA256: **`dc5a7118b33fa84221d1b051997642180ca9c45e1605ebcad7b15a0d0642c7dc`**.
- The source was rehashed at completion; the reviewed file was not edited.
- Archived canonical target: `canonical-target.md`, 3,623 bytes, SHA256 `7416ff9dbadb6ac3e590520edf03b63cac861e5f76f930294d88e172bad0858d`.
- I also read the canonical page directly from current `refs/remotes/upstream/main` at commit `1f22006bdaa4659fcaa0bb775a887685cd3cc566`, path `eigenvalues-and-inverse-problems/SP-13/README.md`.

## 1. Exact-target match

The target permits an arbitrary sequence of complex perturbations $E_n$, subject only to $\|E_n\|_*/n\to0$. The base matrices $H_n$ are Hermitian, with the prescribed spectral distribution against every complex-valued $F\in C_c(\mathbb C)$. Neither the base nor perturbation sequence is assumed bounded in spectral norm. The conclusion concerns empirical eigenvalue distributions, with algebraic multiplicity, not individual eigenvalue matching.

The candidate proves this statement in full. It never assumes that $H_n+E_n$ is normal or diagonalizable. Its measurable real symbol on $[0,1]$ is exactly the canonical normalization. No bound on the symbol or either matrix sequence is inserted in the limiting argument.

I directly opened the primary Barbarino–Serra-Capizzano paper, Conjecture 1 in Section 6, printed page 29, and checked that this is the conjecture being addressed:
https://giovannibarbarino.github.io/doc/articles/NHperturbation.pdf ; DOI https://doi.org/10.1002/nla.2286 .

## 2. Essential external theorem checked in the primary source

I directly opened N. Randrianantoanina, *Spectral subspaces and non-commutative Hilbert transforms*, Colloquium Mathematicum91(2002),9–27:
https://www.impan.pl/shop/en/publication/transaction/download/product/87479 ; DOI https://doi.org/10.4064/cm91-1-2 .

Theorem4.8 on printed page23, continued on page24, supplies an absolute weak-type constant for triangular truncation along an arbitrary finite family of orthogonal projections. Its input is unrestricted in $L^1$, not necessarily positive or self-adjoint. The weak quasi-norm on printed page12 is the supremum of threshold times the trace of the corresponding singular-value spectral projection. The setup allows the ordinary, unnormalized finite-matrix trace. With rank-one projections this is precisely

$$
\#\{j:\sigma_j(\mathcal T_+X)>s\}\le C\|X\|_*/s.
$$

The lower-triangular convention in the source becomes the required upper-triangular convention by reversing projection order. The same absolute constant works for every matrix size. The source credits Dodds–Dodds–de Pagter–Sukochev, Theorem1.4, and also gives a proof via its Hilbert-transform result. The candidate preserves that attribution. I checked the primary statement and its specialization; I am relying on the cited published theorem, not claiming a new proof of its entire operator-algebra foundation.

Primary file fingerprints checked:

- `Randrianantoanina-2002.pdf`: 229,511 bytes, SHA256 `5ae7290c48951f713535e2051817d1cc92de1a4e7b8532817fd9b8e26ca58870`.
- `NHperturbation.pdf`: 1,025,193 bytes, SHA256 `70f187cb5760a97e90944ba1754f701a028746050fc70397bfea31d76ab3eea4`.

## 3. Independent reconstruction of the Schur estimate

Set $q=\|E\|_*$. In a unitary Schur decomposition, write

$$
U^*(H+E)U=D+iJ+N=G+Z,
$$

where $D,J$ are real diagonal, $N$ is strictly upper triangular, $G=U^*HU$ is Hermitian and $Z=U^*EU$. Thus $K=\operatorname{Im}(D+iJ+N)=\operatorname{Im}Z$, so $\|K\|_*\le q$ by the triangle inequality and adjoint invariance of the trace norm.

For $i<j$, the corresponding entry of $K$ is $N_{ij}/(2i)$; hence $N=2i\mathcal T_+(K)$. Applying the published theorem gives $n_N(s)\le2Cq/s$. No independent perturbation or artificial error is introduced by selecting a Schur basis.

I separately verified the elementary counting inequality $n_{X+Y}(a+b)\le n_X(a)+n_Y(b)$ by truncating singular components above $a,b$. It is valid with the strict thresholds used in the manuscript, including equality at a threshold. Applying it to $N/2$ and $N^*/2$ gives $n_{\operatorname{Re}N}(s)\le2n_N(s)\le4Cq/s$.

The Hermitian-part identity is $D-G=\operatorname{Re}Z-\operatorname{Re}N$. Splitting the threshold at $s/2$, and using the trace-norm bound on $\operatorname{Re}Z$, yields exactly

$$
n_{D-G}(s)\le(2+8C)q/s.
$$

The signs and constants in equations(7)–(10) are therefore correct. Every constant is independent of matrix size, the Schur ordering, the norm of $H$, and the norm of $E$ apart from the explicit factor $q$.

The diagonal of $K$ is $J$. Pairing $K$ with the diagonal matrix of signs of its real diagonal entries, whose operator norm is at most one, gives $\sum_j|J_{jj}|\le\|K\|_*\le q$. This verifies equation(11), including zero entries, without using a false trace-norm boundedness statement for triangular truncation.

## 4. Hermitian transfer lemma

For each fixed $s>0$, the spectral decomposition of a Hermitian difference $A_n-B_n$ splits it into a rank-$o(n)$ Hermitian part $R_n$ and a Hermitian part $S_n$ with norm at most $s$. The candidate uses the strict cutoff above $s$, so the residual bound is valid at equality.

For a Hermitian rank-$r$ change, min-max gives a discrepancy at most $r$ between eigenvalue counting functions at every real threshold. Integrating against $g'$ gives equation(6) for $g\in C_c^1(\mathbb R)$; compact support removes endpoint terms even if the matrix eigenvalues are arbitrarily large. This also holds for complex-valued $g$ by the same absolute-value bound.

For the remaining norm-$s$ change, ordered Hermitian eigenvalues move by at most $s$. Its normalized trace effect is at most the global modulus of continuity $\omega_g(s)$. The quantifiers are in the correct order: fix $s$, let $n$ tend to infinity, then let $s$ decrease to zero. Uniform approximation of $C_c$ functions by $C_c^1$ functions proves the general lemma. No tightness, spectral cutoff, or unmentioned operator-norm hypothesis is needed for this argument.

## 5. Full complex test-function limit

Equation(10) divided by $n$ verifies the transfer lemma for $D_n$ and $U_n^*H_nU_n$. For every $F\in C_c(\mathbb C)$, its restriction to the real axis belongs to $C_c(\mathbb R)$, proving equation(12).

Equation(11) bounds the fraction of diagonal imaginary parts above a fixed threshold $s$ by $q_n/(ns)$. A continuous compactly supported function on the plane is globally uniformly continuous. On the other indices the change in its value is bounded by $\omega_F(s)$; on the exceptional indices it is at most $2\|F\|_\infty$. This yields equation(13) exactly. Again, first letting $n\to\infty$ and then $s\downarrow0$ is valid. The Schur diagonal lists all eigenvalues with algebraic multiplicity, so the resulting average is the required empirical eigenvalue average.

Combining this with the assumed distribution of $H_n$ proves the full displayed target for every permitted $F$ and measurable real symbol. Large individual eigenvalues or singular values do not invalidate any step.

## 6. Conclusion and limits of this audit

**PASS:** no mathematical gap was found, and the exact canonical SP-13 conjecture follows from the supplied argument and the correctly scoped published weak-type theorem. A bound for one special perturbation class, a genericity result, or a numerical experiment is not being substituted for the full target.

No candidate file was changed by this reviewer. No numerical testing was required for this argument. The frozen candidate's independent-review disclosure should be updated only in any later presentation metadata, with this exact original review and source retained for provenance. Any later substantive mathematical edits require another review. Publication eligibility and final source/PDF equivalence remain separate checks for the submission process.
