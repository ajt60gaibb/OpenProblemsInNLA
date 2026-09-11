# Independent agent proof review: KE-04

- **Verdict: PASS.** The proof establishes strict interval occupancy for every iteration pair and index in the displayed KE-04 target, including possible eigenvalue multiplicities and the coincident-endpoint case.
- **Review date:** 11 September 2026.
- **Reviewer:** independent verification agent `/root/review_sp05_ke04`.
- **Target read:** [KE-04/README.md](../../../../eigenvalues-and-inverse-problems/KE-04/README.md), specifically its complete original problem statement.
- **Proof read:** [KE-04/solution.md](../../../../eigenvalues-and-inverse-problems/KE-04/solution.md), Theorem KE-04 and sections 1–3.
- **Proof SHA-256:** `3ba1bd9a62a00aaf787758af6312e4787ca8d6db02b4487e8b956ce0553977a7`.
- **Hash convention:** UTF-8 bytes of the substring beginning at `## Theorem ` and ending immediately before `## Scope and review notes`, after replacing CRLF and CR with LF and stripping leading/trailing whitespace. The resulting block has 2622 bytes.

## Exact scope and method

The target assumes real symmetric A, an n-by-p full-column-rank starting block V, and full block Krylov dimension through iteration s. For every `1 <= k < j <= s` and `1 <= i <= (k-1)p`, it asks whether the open interval between Ritz values `theta_i^(k)` and `theta_(i+p)^(k)` contains a Ritz value from iteration j. Values are ordered with multiplicity. I independently checked the entire proof against this quantification, including the rank hypothesis and both endpoints of each index range. I did not use the supporting diagnostics, earlier claimed checks, or a presumption that the theorem was correct.

The review certifies only the derivation in the hashed block against the local target. It does not establish novelty, literature completeness, finite-precision behavior, or consistency of separately generated PDF/LaTeX artifacts.

## Checked derivations

### 1. Full dimension and the compression formulation

Write `K_l = range[V, AV, ..., A^(l-1)V]`. The nesting `K_l subset K_(l+1)` and the relation `A K_l subset K_(l+1)` follow directly from this definition. Full dimension `dim K_s = sp` means that all sp columns of the displayed block Krylov matrix are linearly independent. Every prefix is therefore linearly independent, giving `dim K_l = lp` for all l <= s. Thus the proof's formulation with full dimension at s supplies the target's needed full dimension at every earlier iteration. Maximality of s is not otherwise required.

For the orthogonal projector P_l, the operator `H_l = P_l A|_(K_l)` is self-adjoint on K_l: for x,y in K_l, `<x,H_l y> = <x,Ay> = <Ax,y> = <H_l x,y>`. If Q_l is any orthonormal basis matrix, its matrix representation is exactly `Q_l^T A Q_l`. The proof therefore uses exactly the target spectra, without needing a compatible choice of bases or an explicit Lanczos recurrence.

### 2. The proposed spectral gap and the intersection vector

For k = 1, the range `1 <= i <= (k-1)p` is empty, so the statement is vacuous. For an admissible k >= 2, set `a = theta_i^(k)`, `b = theta_(i+p)^(k)`. The upper index is valid because `i+p <= kp`; sorted eigenvalues give a <= b.

For `q(t) = (t-a)(t-b)`, q is nonnegative outside (a,b). If H_j has no eigenvalue in that interval, its orthogonal spectral decomposition implies `q(H_j) >= 0`. This remains true when a = b, since q is then a square.

Choose an orthonormal eigenbasis of H_k and take E to be the span of vectors numbered i through i+p. These are p+1 distinct basis vectors even if some or all eigenvalues coincide, so `dim E = p+1`. Every corresponding eigenvalue lies in [a,b], where q <= 0, hence `<x,q(H_k)x> <= 0` for every x in E.

Both E and K_(k-1) are subspaces of the kp-dimensional K_k. Full block dimension gives `dim K_(k-1) = (k-1)p`, so

`dim(E intersect K_(k-1)) >= (p+1) + (k-1)p - kp = 1`.

Consequently the proof may choose a nonzero real x in this intersection. The dimension argument does not require E to be the entire eigenspace of any repeated eigenvalue.

### 3. Equality of quadratic forms

Since x is in K_(k-1), Ax lies in K_k and hence in K_j. Therefore `H_k x = H_j x = Ax`. For either self-adjoint compression H_l with l equal to k or j,

`<x,H_l^2 x> = ||H_l x||^2 = ||Ax||^2`.

Expanding q then gives, for both l,

`<x,q(H_l)x> = ||Ax||^2 - (a+b)<x,Ax> + ab||x||^2`.

This verifies the exact equality claimed. It does not assume `H_k^2 x = A^2 x`, which need not hold and is not needed. Because x lies in E, the common quadratic form is nonpositive; because q(H_j) is positive semidefinite, it is also nonnegative. Hence it is zero. For a positive-semidefinite self-adjoint matrix, a zero quadratic form forces the vector into its kernel, as is immediate by summing its nonnegative eigenvalue-weighted squared coordinates. Thus `q(H_j)x = 0` follows legitimately.

### 4. Passing from the compression to A

The vector x lies in K_(k-1), so `A^2 x` lies in K_(k+1). The integer inequality k < j ensures `k+1 <= j`, and consequently `A^2 x` belongs to K_j. Since H_j x = Ax,

`H_j^2 x = P_j A(Ax) = P_j A^2 x = A^2 x`.

Together with `H_j x = Ax`, this proves `q(H_j)x = q(A)x`. Hence the preceding kernel conclusion really gives `q(A)x = 0` in the ambient space. No invariance of all of K_j under A is assumed; only the stated inclusion for this particular vector and its first two images is used.

### 5. Full block rank gives the contradiction

Membership in K_(k-1) gives a representation

`x = sum_(l=0)^(k-2) A^l V c_l`.

The prefix block matrix has full column rank, so this representation is unique; in any event x != 0 ensures that not all c_l are zero. Let r be the largest index with c_r != 0. Multiplication by the monic quadratic q produces

`q(A)x = sum_(l=0)^r [A^(l+2)V c_l - (a+b)A^(l+1)V c_l + ab A^l V c_l]`.

The coefficient at the highest displayed power, `A^(r+2)V`, is precisely c_r: the two lower-degree parts could contribute there only from c_(r+1) or c_(r+2), both zero by the definition of r. Thus the block coefficient vector of this expression is nonzero.

Because r <= k-2, all powers in that expression range from zero to at most k. Since `k+1 <= j <= s`, the matrix `[V, AV, ..., A^k V]` consists of a prefix of the full-rank matrix at iteration s and has full column rank. It therefore maps the nonzero coefficient vector just identified to a nonzero vector. This proves `q(A)x != 0`, contradicting the conclusion of the preceding step.

The contradiction excludes the supposed absence of a later Ritz value from (a,b). Every admissible pair (k,j) and every admissible index i was arbitrary, so it proves the full requested statement.

## Gap search and boundary cases

No mathematical gap was found. The quadratic-form step was checked separately from the stronger operator identity, so no unsupported replacement of the square of a compression by the compression of a square occurs. Full rank is invoked precisely at iteration k+1, which exists even for the boundary pair k = s-1, j = s. The argument does not require full dimension at j+1 or assume that A has a simple spectrum.

At i = 1 and i = (k-1)p, all selected indices remain in 1 through kp, and E still has dimension p+1. At k = 2, the representation of x has only the V term, and its nonzero leading coefficient is tested against `[V, AV, A^2 V]`, as required. For s <= 2 there is no pair with both k >= 2 and k < j, so the entire assertion is vacuous. The proof also applies when p = 1, the scalar case.

When a = b, q(t) = (t-a)^2 is nonnegative on the whole line, while it vanishes on E. Every subsequent step is unchanged, and the same rank contradiction results. Thus coincident endpoints in the stated index range are actually excluded under the hypotheses; the proof does not assume their separation in advance. Multiplicities smaller than this obstruction are allowed throughout.

The conclusion is strictly for exact arithmetic with no loss of full block dimension through the relevant iteration. A deflated starting sequence or a finite-precision Lanczos computation need not satisfy those hypotheses and is outside this review's conclusion.

## Review limits

PASS means that this independent agent audit verified the full local target from the supplied proof and found no gap. It is an agent review, not external human peer review, a formal proof certificate, or an assertion of mathematical priority. No manuscript, catalog status, code, or remote file was changed by this reviewer.
