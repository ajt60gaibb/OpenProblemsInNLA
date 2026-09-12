# KE-05: failure of spectrum-uniform probabilistic interpolation bounds

Private full-proof candidate, prepared on 12 September 2026 UTC.
The proposed author of a possible submission is George Stepaniants,
Department of Computing and Mathematical Sciences,
California Institute of Technology.
This document was developed with substantial AI assistance and is awaiting
an independent mathematical review. It is not a public submission or a
claim of human or formal verification.

## Exact target and conclusion

The canonical KE-05 question fixes integers $b\geq1$ and $d\geq2$ and asks
whether the random variable $\chi_{\rm mono}\chi_{\rm coef}$ defined by
its stated recurrence is uniformly bounded in probability over all real
diagonal blocks with pairwise disjoint spectra. In particular, for each
$0<\delta<1$ there should be a finite $C(b,d,\delta)$ that works for
every fixed admissible diagonal input. All matrix norms are spectral
norms, and all entries of the square matrices $\Omega_i$ are independent
standard real Gaussian variables.

The answer to this exact question is **no**. The failure occurs already
for $b=2$ and $d=3$, with deterministic admissible inputs
$$
\Lambda_1=2I_2,\qquad
\Lambda_2(\varepsilon)=
\begin{pmatrix}\varepsilon&0\\0&2\varepsilon\end{pmatrix},
\qquad
\Lambda_3=
\begin{pmatrix}0&0\\0&1\end{pmatrix},
\qquad 0<\varepsilon<\frac14.
$$
Their spectra are pairwise disjoint. The repeated eigenvalue within the
first block is permitted by the canonical hypotheses. For every finite
real number $C$,
$$
\lim_{m\to\infty}
\Pr\!\left\{
\chi_{\rm mono}\bigl(\varepsilon_m\bigr)
\chi_{\rm coef}\bigl(\varepsilon_m\bigr)\leq C
\right\}=0,
\qquad
\varepsilon_m=\frac1{m+5},\quad m=1,2,\ldots.
$$
Thus even the choice $\delta=1/2$ admits no finite uniform constant.
The proof uses the literal canonical recurrence, without relying on a
matrix-polynomial factorization theorem.

## 1. Recurrence and the particular ordering

For completeness, in any of the orderings prescribed in KE-05, the
recurrence is computed in descending order of $i$:
$$
B_i=\Omega_i^{-1}\Lambda_i\Omega_i,\qquad
S_{i,i}=I_2,\qquad
S_{i,j}=B_iS_{i,j-1}-S_{i,j-1}\widehat B_j
\quad(j=i+1,\ldots,3),
$$
$$
\widehat\Omega_i=\Omega_i S_{i,3},\qquad
\widehat B_i=\widehat\Omega_i^{-1}\Lambda_i\widehat\Omega_i
              =S_{i,3}^{-1}B_iS_{i,3}.
$$
The superscript $(k)$ denotes the ordering whose first original block
is $k$, as in the canonical statement. The global quantities are the
maxima of their respective ordering-specific quantities.

We obtain lower bounds from ordering $k=1$, which is the original
ordering $(1,2,3)$, and omit its superscript in intermediate formulas.
The global endpoints for our diagonal input are $a=0$ and $c=2$.
Consequently, the $i=2$ term in the definition of the first maximum gives
$$
\chi_{\rm mono}\geq\chi_{\rm mono}^{(1)}
\geq
\frac{\|\widehat B_2\|_2}{\|\Lambda_2(\varepsilon)\|_2}
=\frac{\|\widehat B_2\|_2}{2\varepsilon}.
$$
No zero-over-zero convention is involved in this particular ratio.

The first-block minimum cross-gap is exactly one:
$$
\min_{\substack{i=2,3,\ \lambda\in\sigma(\Lambda_1)\\
                         \eta\in\sigma(\Lambda_i)}}
|\lambda-\eta|
=\min\{2-\varepsilon,\,2-2\varepsilon,\,2,\,1\}=1.
$$
Since $d-1=2$, it follows that
$$
\chi_{\rm coef}\geq\chi_{\rm coef}^{(1)}
=\|S_{1,3}^{-1}\|_2^{1/2}.
$$

## 2. An almost-sure nonzero limit of the transformed second block

Work first on the event that $\Omega_2$ and $\Omega_3$ are invertible,
which has probability one. Put
$$
X=\Omega_2^{-1}
\begin{pmatrix}1&0\\0&2\end{pmatrix}\Omega_2,
\qquad
P=\Omega_3^{-1}
\begin{pmatrix}0&0\\0&1\end{pmatrix}\Omega_3.
$$
Then $B_2=\varepsilon X$, $B_3=P$, $\det X=2$, and
$$
P^2=P,\qquad \operatorname{tr}P=1,\qquad
\det P=0,\qquad \operatorname{adj}P=I_2-P.
$$
Here $\operatorname{adj}$ is the classical adjugate. Define the real
random scalar and matrix
$$
\kappa=\operatorname{tr}\bigl((I_2-P)X\bigr),
\qquad Q=(I_2-P)XP.
$$
The last block is unchanged by the recurrence, so
$$
\widehat B_3=P,\qquad
S_{2,3}=\varepsilon X-P,\qquad
\widehat B_2=(\varepsilon X-P)^{-1}
                  \varepsilon X(\varepsilon X-P).
$$
The elementary $2\times2$ determinant expansion yields
$$
\det(\varepsilon X-P)
=\varepsilon^2\det X
 -\varepsilon\operatorname{tr}\bigl((\operatorname{adj}P)X\bigr)
 +\det P
=\varepsilon(2\varepsilon-\kappa).
$$
The adjugate is linear on $2\times2$ matrices. Hence, whenever this
determinant is nonzero, cancellation of the scalar factor $\varepsilon$
gives the exact formula
$$
\widehat B_2=
\frac{\bigl(\varepsilon\operatorname{adj}X-(I_2-P)\bigr)
             X(\varepsilon X-P)}
     {2\varepsilon-\kappa}.
$$
On the event $\kappa\ne0$, this formula is defined for all sufficiently
small positive $\varepsilon$ and has the limit
$$
\widehat B_2\longrightarrow
N:=-\frac{(I_2-P)XP}{\kappa}=-\frac Q\kappa
\qquad(\varepsilon\downarrow0).
$$
The identity $P(I_2-P)=0$ also gives $N^2=0$.
We next show that this limiting nilpotent matrix is nonzero almost
surely; it is not being assumed to be nonzero merely because the
recurrence is nonsingular.

The entries of $X$ and $P$, and therefore $\kappa$ and the entries of
$Q$, are rational functions of the eight real entries of
$\Omega_2,\Omega_3$. Their denominators can be cleared by products of
determinants of these two matrices. Consider the invertible rational
matrices
$$
\Omega_2=I_2,\qquad
\Omega_3=
\begin{pmatrix}1&2\\3&5\end{pmatrix}.
$$
At this single deterministic witness,
$$
X=\begin{pmatrix}1&0\\0&2\end{pmatrix},\qquad
P=\begin{pmatrix}6&10\\-3&-5\end{pmatrix},\qquad
\kappa=7,\qquad
Q=\begin{pmatrix}30&50\\-18&-30\end{pmatrix}.
$$
In particular, the numerator polynomials of $\kappa$ and of the
$(1,1)$ entry of $Q$ are not identically zero. A nonzero polynomial in
finitely many real variables has a Lebesgue-null zero set. One elementary
proof is induction on the number of variables: outside the common zero
set of the coefficient polynomials, each univariate slice has finitely
many roots, and Fubini's theorem finishes the induction. Since the joint
Gaussian law has a density, each of these zero sets has probability
zero. Together with almost-sure invertibility of the two Gaussian
matrices, this proves
$$
\Pr\{\kappa\ne0,\ Q_{11}\ne0\}=1.
$$
It follows that
$$
\|\widehat B_2(\varepsilon)\|_2\longrightarrow\|N\|_2>0
\quad\text{almost surely as }\varepsilon\downarrow0
$$
along values where the recurrence is defined. The matrix-norm limit
uses only continuity of the spectral norm.

For an additional exact check at the displayed rational witness,
$$
\widehat B_2
=\frac1{2\varepsilon-7}
\begin{pmatrix}
2\varepsilon^2-7\varepsilon+30&20\varepsilon+50\\
3\varepsilon-18&4\varepsilon^2-14\varepsilon-30
\end{pmatrix},
$$
and
$$
N=\frac17\begin{pmatrix}-30&-50\\18&30\end{pmatrix},
\qquad \|N\|_2=\frac{68}{7}.
$$
The witness is used to prove that the relevant polynomials are
nonzero. The counterexample does not require drawing that particular
Gaussian outcome, an event of probability zero.

## 3. A deterministic lower bound for the coefficient factor

Because $\Lambda_1=2I_2$, we have $B_1=2I_2$ regardless of $\Omega_1$.
The literal recurrence therefore gives
$$
S_{1,2}=2I_2-\widehat B_2,\qquad
S_{1,3}=2S_{1,2}-S_{1,2}P
       =(2I_2-\widehat B_2)(2I_2-P).
$$
This particular factorization uses the scalar identity $B_1=2I_2$ and
does not reorder two noncommuting factors. Whenever $S_{2,3}$ is
invertible, $\widehat B_2$ is similar to
$\Lambda_2(\varepsilon)$. Thus
$$
\det S_{1,3}
=\det(2I_2-\widehat B_2)\det(2I_2-P)
=2(2-\varepsilon)(2-2\varepsilon).
$$
For $0<\varepsilon<1/4$, this determinant is positive and less than
eight. In particular, $S_{1,3}$ is invertible without any further
restriction on the Gaussian outcome for this ordering.

For any invertible $2\times2$ matrix $S$, its singular values
$s_1\geq s_2>0$ satisfy
$s_2^2\leq s_1s_2=|\det S|$. Consequently
$$
\|S^{-1}\|_2=\frac1{s_2}\geq|\det S|^{-1/2}.
$$
Using the unit cross-gap established in Section 1, we obtain
$$
\chi_{\rm coef}
\geq\|S_{1,3}^{-1}\|_2^{1/2}
\geq\bigl[2(2-\varepsilon)(2-2\varepsilon)\bigr]^{-1/4}
\geq8^{-1/4}.
$$
In particular, this factor cannot cancel the divergence of the
monomial factor.

## 4. All prescribed orderings are defined almost surely

We give the short genericity argument explicitly so that this proof
does not need a nonsingularity theorem about matrix-polynomial
factorizations.

Fix any one value $0<\varepsilon<1/4$ and any ordering required by
KE-05. The entries produced by the finite recurrence are rational
functions of the entries of the three matrices $\Omega_i$ as long as
the preceding inverses exist. Set $\Omega_1=\Omega_2=\Omega_3=I_2$.
For this deterministic witness all $B_i$ are diagonal, and induction
down the recurrence gives
$$
\widehat B_i=B_i=\Lambda_i,\qquad
S_{i,j}=\prod_{\ell=i+1}^{j}(\Lambda_i-\Lambda_\ell)
$$
in the chosen ordering. The empty product is $I_2$. Every diagonal
entry of each factor is nonzero, since the spectra of different blocks
are disjoint. Thus every matrix whose inverse is required is
invertible at this witness.

Proceeding through the finite list of inverses, each determinant,
written as a rational function with the previously encountered
denominators cleared, has a numerator polynomial that is nonzero at
this witness. The exceptional set is therefore contained in a finite
union of zero sets of nonzero polynomials. It is Lebesgue-null and
hence has Gaussian probability zero. This applies to the finitely
many root orderings simultaneously.

Apply this argument to each member of the deterministic sequence
$\varepsilon_m=1/(m+5)$, $m\geq1$. A countable union of null sets is
null, so with probability one every prescribed ordering is defined
for every member of this sequence. The endpoint convention in the
canonical question makes any scalar-block $0/0$ ratio equal to one;
it does not affect the lower bounds above.

## 5. Failure of every finite uniform probability bound

Couple the inputs at different $\varepsilon_m$ by using the same
three Gaussian matrices $\Omega_1,\Omega_2,\Omega_3$ at every index.
For each fixed index this coupling has exactly the distribution
specified in KE-05: the diagonal input is deterministic and the
entries of all three matrices are independent standard Gaussians.

On a probability-one event, the conclusions of Sections 2 and 4
hold together. On that event the global constants are defined for
every $m$ and satisfy
$$
\chi_{\rm mono}(\varepsilon_m)\chi_{\rm coef}(\varepsilon_m)
\geq
8^{-1/4}\,
\frac{\|\widehat B_2(\varepsilon_m)\|_2}{2\varepsilon_m}
\longrightarrow+\infty.
$$
For any finite real $C$, the indicators of the events that these
products are at most $C$ therefore converge almost surely to zero.
They are bounded by one, so the dominated convergence theorem yields
$$
\Pr\!\left\{
\chi_{\rm mono}(\varepsilon_m)\chi_{\rm coef}(\varepsilon_m)\leq C
\right\}\longrightarrow0.
$$
Changing the constants arbitrarily on the probability-zero sets where
an inverse is undefined does not change this conclusion.

If the asserted $C(2,3,1/2)$ existed, each probability in the last
display with that finite threshold would be at least $1/2$, a
contradiction. This disproves the canonical uniform-in-eigenvalues
claim.

The coupling is only a proof device for the marginal-probability
limit. No input eigenvalue depends on a sampled Gaussian matrix, and
no stronger requirement that one Gaussian draw succeed for every
spectrum is imposed on the conjecture.

## Scope, attribution, and verification limits

The negative result concerns the random constants defined by the
literal canonical KE-05 recurrence. Its input uses interlaced block
spectra: the eigenvalues of $\Lambda_2$ lie between those of
$\Lambda_3$. Pairwise disjoint spectra permit this. The argument makes
no assertion about a different question imposing ordered, disjoint
spectral intervals on the blocks, and it does not disprove
cluster-robust convergence of a block Krylov algorithm itself.

Nian Shao introduced the source interpolation framework and the
conjectured spectrum-independent probabilistic bounds in
*A structural bound for cluster robustness of randomized small-block
Lanczos*, arXiv:2507.10144v2, 30 May 2026; relevant locators are the
recurrence in Lemma 3, equation (12), and Conjecture 1 in Section 3.2.
The canonical problem and these source locations were read for scope.
The proof here consists of elementary $2\times2$ identities,
Gaussian absolute continuity, and dominated convergence. It does not
depend on the correctness of a general ordered-product identity in
that paper.

The accompanying exact-arithmetic checker verifies the displayed
rational witness, polynomial identities at that witness, and selected
finite-input recurrence instances. Those checks support transcription
and algebra; the general probability proof is the argument above.
An independent review, a current public eligibility audit, and any
eventual publication are separate steps.

## Primary references

1. Canonical KE-05, *Spectral-gap-independent constants for randomized
   block polynomial interpolation*:
   <https://github.com/MColbrook/OpenProblemsInNLA/blob/main/randomized-and-low-rank-approximation/KE-05/README.md>.
2. N. Shao, *A structural bound for cluster robustness of randomized
   small-block Lanczos*, arXiv:2507.10144v2, 30 May 2026:
   <https://arxiv.org/html/2507.10144v2>.
