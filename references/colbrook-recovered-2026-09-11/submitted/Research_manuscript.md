# Recovered numerical linear algebra proof drafts

Seven notes cover eight candidate results. Independent review and source matching are required. See [STATUS.md](STATUS.md), [SOURCES.md](SOURCES.md), and [the recovery record](research/RECOVERY_AND_CORRECTIONS.md). Local IE labels are provisional; six finite-certificate groups pass, while the two row-deletion results remain analytic drafts.



---

# Sharp partial-pivoting growth for unequal bandwidths

*Reconstructed candidate proof draft. Independent mathematical review and source/priority verification are required. The IE identifiers are provisional labels recovered from earlier notes, not verified current repository identifiers.*

## Statement

Let $A\in\mathbb R^{n\times n}$ or $\mathbb C^{n\times n}$ be nonsingular, with $a_{ij}=0$ whenever $i>j+p$ or $j>i+q$. Normalize $\max|a_{ij}|=1$. Growth includes all active Schur-complement entries, not merely $U$. Define $G(p,q)$ as the supremum over permitted orders and pivot paths.

**Theorem 1**. *$G(0,q)=1$. For $p\ge1$, 

$$
h_t=0\ (t\le0),\qquad h_t=1+\sum_{r=1}^p h_{t-r}\ (t\ge1),\qquad
 \boxed{G(p,q)=h_{p+q}.}
$$

 A real matrix of order $2p+q+1$ attains the bound.*

The recurrence gives 

$$
\begin{aligned}
G(p,0)&=2^{p-1},\\
G(p,q)&=2^{p+q-1}-(q-1)2^{q-2}\quad(1\le q\le p+1),\\
G(1,q)&=q+1,\qquad G(2,q)=F_{q+4}-1,
\end{aligned}
$$

 where $F_0=0,F_1=1$. In particular the equal-bandwidth specialization is $2^{2p-1}-(p-1)2^{p-2}$. These identities follow by induction.

## Sorted-front lemma

Suppose a front has $p+1$ target-column magnitudes $y_1\ge\cdots\ge y_{p+1}\ge0$. Remove the row with target magnitude $y_a$ and update the others with multipliers of modulus at most one. The sorted survivors are bounded componentwise by 

$$
(y_1+y_2,y_1+y_3,\ldots,y_1+y_{p+1}).
$$

 Indeed, the triangle inequality bounds each survivor by $y_a+y_i$. For $i<a$, $y_a+y_i\le y_1+y_{i+1}$, since $y_i-y_{i+1}\le y_1-y_a$. For $i\ge a$, the ordered bound is $y_a+y_{i+1}\le y_1+y_{i+1}$. Sorting and appending a fresh value are monotone. Thus always eliminating the largest target-column magnitude gives a componentwise upper envelope, even though GEPP actually chooses by another column.

Start with $p$ zeros, append a fresh $1$, and perform this envelope update. After one update all survivors equal $1$. Subsequently the ordered state evolves by 

$$
(x_1,\ldots,x_p)\mapsto(x_1+x_2,\ldots,x_1+x_p,x_1+1).
$$

 After $t\ge1$ updates its $i$th entry is 

$$
x_i^{(t)}=1+\sum_{r=1}^{p-i+1}h_{t-r},
$$

 so its largest entry is $h_t$. Direct substitution proves this identity, including $p=1$.

## Upper bound

At the start of stage $k$, original rows with labels $i\ge k+p$ are unchanged by earlier stages: their first $k-1$ original entries are zero. They have zero earlier multipliers and cannot be selected as nonzero earlier pivots. Thus there are at most $p$ old surviving rows plus fresh original row $k+p$; later rows are untouched. Near the bottom, missing fresh rows can be padded by zeros.

Fix target column $j$ and set $L=p+q$. For $j\ge L+1$, all target entries in the front are zero until stage $k_0=j-L$, when original row $j-q$ arrives. Exactly $L$ updates occur from $k_0$ through $j-1$. Each fresh target entry has modulus at most one, so the lemma bounds every value by $h_L$. For $j\le L$, the initial $p$ old values are bounded by the canonical state after one imaginary update. At most $j-1$ actual updates precede elimination of column $j$, giving $h_j\le h_L$. Recorded pivot-row entries and untouched entries satisfy the same bound. This covers every active entry. For $p=0$ the matrix is upper triangular and all elimination multipliers vanish.

## Attaining construction

For $p\ge1$, put $j=p+q+1$, $n=j+p$, and let $L_0$ be unit lower triangular with $-1$ on its first $p$ subdiagonals. Use the original-row order 

$$
\sigma=(p+1,1,2,\ldots,p,p+2,\ldots,n),\qquad (Pa)_i=a_{\sigma_i},\qquad \eta=2^{-p}.
$$

 For $k<j$, define an upper-supported vector $u^{(k)}$ by 

$$
u_i^{(k)}=\begin{cases}
1&i=1,\ k\le p+1,\\
2^{i-2}&2\le i\le k\le p+1,\\
1&i=k,\ k\ge p+2,\\
0&\text{otherwise},
\end{cases}
\qquad A_{:,k}=\eta P^TL_0u^{(k)}.
$$

 Set 

$$
A_{i,j}=\begin{cases}1&p+1\le i\le n,\\0&i\le p,\end{cases}
\qquad A_{:,k}=e_k\quad(k>j).
$$

 For $k\le p+1$, the first entry of $L_0u^{(k)}$ is $1$, entries $2,\ldots,k$ are zero, and later entries are negatives of sums of subsets of $u^{(k)}$. Their moduli are at most $2^{k-1}\le2^p$. After row-label assignment, support lies in original rows $k,\ldots,k+p$. For $k\ge p+2$ the same support follows from $L_0e_k$. Hence these columns have lower bandwidth at most $p$ and upper bandwidth zero, with entries bounded by one. The target column starts at $p+1=j-q$ and ends at $n=j+p$. Later identity columns respect the band. The initial maximum is one.

In the first $j-1$ stages in row order $\sigma$, the factorization gives multipliers in $\{0,-1\}$ and nonzero pivots. After earlier eliminations, active column $k$ is $L_{0,ik}U_{kk}$; the diagonal multiplier is one, so each chosen pivot is maximal in modulus. Thus these are admissible GEPP choices, not an extra preliminary permutation.

For the target column, $c=PA_{:,j}$ has $c_1=1$, $c_i=0$ for $2\le i\le p+1$, and $c_i=1$ for $i\ge p+2$. Forward substitution gives 

$$
u_i=c_i+\sum_{r=1}^p u_{i-r},\qquad u_i=0\ (i\le0).
$$

 Induction gives $u_1=1$ and $u_i=h_{i-1}$ for $i\ge2$. Therefore the active $(j,j)$ entry at stage $j$ equals $h_{p+q}$. The leading $j\times j$ block has nonzero pivots, and later columns are identity columns; the matrix is block lower triangular with nonsingular diagonal blocks. This proves attainment.

## Checks and source status

The standard-library exact verifier checks 60 attaining matrices ($1\le p\le6$, $0\le q\le9$), their support, pivot admissibility, growth, and nonsingularity, plus recurrence identities. These finite checks are not a formal proof of all orders.

Recovered target description: *Sharp growth for unequal lower and upper bandwidths*, provisionally IE-13 in OpenProblemsInNLA. The current repository statement could not be retrieved during reconstruction. The result is therefore submitted for review under the precise hypotheses above, not asserted to resolve a source statement whose scope has been independently verified. Repository supplied for the task:[^IE-13-1]

[^IE-13-1]: <https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/linear-systems-and-elimination>.


---

# Sharp growth for cyclic tridiagonal partial pivoting

*Reconstructed candidate proof draft. Independent mathematical review and source/priority verification are required. The IE identifiers are provisional labels recovered from earlier notes, not verified current repository identifiers.*

## Statement

Nonzeros are restricted to the ordinary tridiagonal bands and corners $(1,n)$ and $(n,1)$, both required nonzero. Matrices are nonsingular, and initial maximum modulus is one. Growth includes every active Schur-complement entry.

**Theorem 1**. *With $F_0=0,F_1=1$, the largest permitted growth is 

$$
\boxed{c_n=F_{n+1}+1\quad(n\ge4).}
$$

*

The initial values are $6,9,14,22$ for $n=4,5,6,7$.

## Front estimates

At stage $k\le n-2$, two old surviving rows have labels in $\{1,\ldots,k\}\cup\{n\}$. Fresh original row $k+1$ joins them. Other later original rows, except row $n$, are unchanged because their earlier columns are zero. Eliminating one front row leaves two old rows.

For a target column, let old magnitudes be $a\ge b\ge0$ and fresh magnitude be at most $c$. Multipliers have modulus at most one. If $c=0$, the sorted new pair is bounded by $(a+b,a)$: a zero-valued pivot leaves the old pair unchanged, and either old pivot gives this triangle-inequality bound. For arbitrary $c$, the survivor sum is at most 

$$
a+b+c+\max(a,b,c).
$$

 These statements are also valid over the complex field.

## All column histories

In the last column, the initial old pair is bounded by $(1,1)$, and fresh values are zero at stages $1,\ldots,n-3$. After $t$ such updates the pair is bounded by $(F_{t+2},F_{t+1})$. Before stage $n-2$ it is at most $(F_{n-1},F_{n-2})$. The next fresh value is at most one, so the survivor sum is at most 

$$
2F_{n-1}+F_{n-2}+1=F_{n+1}+1.
$$

 The final update uses only these two survivors, so the final scalar and all earlier values satisfy this bound.

Column $1$ has only initial values. In column $2$, the initial pair is at most $(1,0)$ and the first fresh value is at most one, giving bound two. For $3\le j\le n-2$, the old pair in column $j$ is zero until stage $j-2$. Fresh row $j-1$ contributes at most one, leaving a pair bounded by $(1,1)$. At stage $j-1$ another fresh value at most one gives survivors bounded by two. At the stage eliminating column $j$, its newly arriving value is at most one. Thus this entire column history is bounded by two.

Column $n-1$ starts with pair at most $(1,0)$, because of original row $n$. Through stage $n-4$ its fresh values vanish. Before stage $n-3$ its pair is therefore at most 

$$
(a,b)=(F_{n-3},F_{n-4});
$$

 this includes $n=4$. A fresh value at most one gives new maximum at most $2a$ and sum at most $2a+b+1=F_{n-1}+1$. At the next stage another fresh value at most one arrives. Each new survivor is bounded by the larger of the old pair sum and old maximum plus one, both at most $F_{n-1}+1$. This is below the claimed global bound. All columns have now been covered.

## Attaining construction

Let $L$ be unit lower triangular with $-1$ on the first two subdiagonals. Define upper triangular $U$ with 

$$
U_{11}=1,\quad U_{12}=U_{22}=\tfrac12,\quad U_{ii}=1\ (3\le i\le n-1),
$$

 all other nonfinal off-diagonal entries zero, and 

$$
U_{i,n}=F_{i+1}\ (i<n),\qquad U_{n,n}=F_{n+1}+1.
$$

 Put $C=LU$ and assign original rows by 

$$
C_{i,:}=A_{\sigma_i,:},\qquad\sigma=(1,n,2,3,\ldots,n-1).
$$

 Multiplication gives a cyclic tridiagonal $A$, with all entry moduli at most one and $A_{1n}=1$, $A_{n1}=-1$. In particular, the last column of $C$ is $(1,1,0,\ldots,0,1)^T$, by the Fibonacci recurrence. After row assignment, these occupy exactly the allowed rows $1,n-1,n$. The first two columns follow from the displayed half entries; each remaining nonfinal column comes from a diagonal entry of $U$ and the two subdiagonals of $L$. This verifies all structural zeros.

The diagonal of $U$ is nonzero. In original-row pivot sequence $\sigma$, active column $k$ after earlier elimination consists of $L_{ik}U_{kk}$. Since $L_{kk}=1$ and $|L_{ik}|\le1$, every chosen pivot is maximal in modulus. This describes ordinary permitted GEPP choices, not a preliminary column or row reordering. The final pivot is $F_{n+1}+1$ and the initial maximum is one, proving attainment.

## Checks and source status

The verifier constructs and checks the factorization, every structural zero, corner condition, pivot, and intermediate growth for $4\le n\le30$. The general proof still requires independent mathematical review.

Recovered target description: *Sharp growth for cyclic tridiagonal matrices*, provisionally IE-14 in OpenProblemsInNLA. The live statement and identifier have not been independently verified during reconstruction. Repository supplied for the task:[^IE-14-1]

[^IE-14-1]: <https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/linear-systems-and-elimination>.


---

# An exact spectral backward-error counterexample for LSMR

*Reconstructed candidate proof draft. Independent mathematical review and source/priority verification are required. The IE identifiers are provisional labels recovered from earlier notes, not verified current repository identifiers.*

## Definitions and exact iterates

For $r=b-Ax$, define 

$$
\mu(x)=\min\{\left\lVert E\right\rVert_2:(A+E)^T((A+E)x-b)=0\}.
$$

 Only $A$ is perturbed; the norm is spectral. The approximation uses $\eta=\left\lVert r\right\rVert_2/\left\lVert x\right\rVert_2$, $K=(A^T,\eta I)^T$, $v=(r^T,0)^T$, and $\widetilde\mu(x)=\left\lVert KK^\dagger v\right\rVert_2/\left\lVert x\right\rVert_2$. For nonzero $x,r$, projection algebra gives 

$$
\widetilde\mu(x)^2=r^TA\bigl(\left\lVert x\right\rVert_2^2A^TA+\left\lVert r\right\rVert_2^2I\bigr)^{-1}A^Tr.
$$

 Use no damping, $x_0=0$, and 

$$
A=\begin{pmatrix}1&0&0\\0&6&0\\0&0&5\\0&0&0\end{pmatrix},\qquad b=(11,1,1,1)^T.
$$

 The matrix has full column rank. Put $H=A^TA=\operatorname{diag}(1,36,25)$ and $g=A^Tb=(11,6,5)^T$. Exact LSMR minimizes $\left\lVert g-Hx\right\rVert_2$ over $\mathcal K_k(H,g)$. Its first two iterates are 

$$
x_1=\frac{1021}{31201}g=\frac1{31201}(11231,6126,5105)^T,
$$

 

$$
x_2=\frac{16321g-383Hg}{110438}=\frac1{55219}(87659,7599,16865)^T.
$$

 For $V_1=(g)$ and $V_2=(g,Hg)$, direct multiplication checks $x_k\in\operatorname{range}V_k$ and $(HV_k)^T(g-Hx_k)=0$. The columns of $HV_k$ are independent, so these conditions uniquely certify the minimizing iterates. The third is $(11,1/6,1/5)^T$, the exact least-squares solution.

The first residuals are 

$$
r_1=\frac1{31201}(331980,-5555,5676,31201)^T,\quad
r_2=\frac1{55219}(519750,9625,-29106,55219)^T.
$$

 The normal residuals decrease, as required by LSMR: 

$$
\left\lVert A^Tr_1\right\rVert_2^2=\frac{3593700}{31201}>\frac{5336100}{55219}=\left\lVert A^Tr_2\right\rVert_2^2.
$$



## General lower and upper certificates

For nonzero $x$, write $s=\left\lVert x\right\rVert_2^2$, $z=Ax$, $r=b-z$, and 

$$
C=AA^T,\qquad D=\frac{\left\lVert r\right\rVert_2^2I-rr^T+zz^T}{s}.
$$



**Lemma 1**. *If $m>n$ and $0\le t\le1$, then $\mu(x)^2\ge\lambda_{\min}(tC+(1-t)D)$.*

*Proof.* For a feasible $E$ whose new residual is nonzero, let $u$ be its unit direction. Then $(A+E)^Tu=0$, so $\left\lVert E\right\rVert_2^2\ge u^TCu$. The residual is $uu^Tb$, because it is orthogonal to $(A+E)x$. Therefore $Ex=r-uu^Tb$, and $\left\lVert E\right\rVert_2^2\ge\left\lVert r-uu^Tb\right\rVert_2^2/s=u^TDu$. A convex combination proves the claim.

For zero new residual, $Ex=r$, so $\left\lVert E\right\rVert_2^2\ge\left\lVert r\right\rVert_2^2/s$. Choose unit $u\in\ker A^T$, possible since $m>n$. Then $u^Tz=0$ and 

$$
u^T[tC+(1-t)D]u=(1-t)(\left\lVert r\right\rVert_2^2-(u^Tr)^2)/s\le\left\lVert r\right\rVert_2^2/s.
$$

 This proves the same bound in that case. ◻

**Lemma 2**. *If a unit vector $u$ has $u^TCu<\kappa$ and $u^TDu<\kappa$, with $\kappa>0$, then a feasible perturbation has $\left\lVert E\right\rVert_2\le\sqrt\kappa$.*

*Proof.* Let $e=x/\sqrt s$ and prescribe 

$$
E^Tu=-A^Tu=:de+a_\perp,\qquad
Ee=(r-uu^Tb)/\sqrt s=:du+c_\perp,
$$

 where $a_\perp\perp e$, $c_\perp\perp u$, and the shared scalar is $d=-u^TAx/\sqrt s$. The two squared lengths are $u^TCu,u^TDu$. A completion is 

$$
E=due^T+ua_\perp^T+c_\perp e^T-\frac{d}{\kappa-d^2}c_\perp a_\perp^T.
$$

 To bound its norm, put $d_0=d/\sqrt\kappa$, $r_0=\sqrt{1-d_0^2}$. In decompositions along $u,e$, $E/\sqrt\kappa$ factors as 

$$
\begin{pmatrix}1&0\\0&c_\perp/(\sqrt\kappa r_0)\end{pmatrix}
\begin{pmatrix}d_0&r_0\\r_0&-d_0\end{pmatrix}
\begin{pmatrix}1&0\\0&a_\perp^T/(\sqrt\kappa r_0)\end{pmatrix}.
$$

 The outside maps have norm at most one by the prescribed length bounds, and the middle map is orthogonal. The prescriptions give $(A+E)^Tu=0$ and $(A+E)x=(I-uu^T)b$, proving feasibility. ◻

## Strict increase

For $x_1$, choose $w=(250,-1,1,27)^T$, $u=w/\sqrt{63231}$, $\kappa=1979/2000$. Exact evaluation gives 

$$
u^TCu=\frac{62561}{63231}<\kappa,\qquad
u^TDu=\frac{1642993919237}{1713779258646}<\kappa.
$$

 The upper lemma applies. For $x_2$, set $t=5/6$ and $c=99/100$. Then $tC+(1-t)D-cI=K/2407881992100$, where 

$$
\scriptsize
K=\begin{pmatrix}
206417059721&-50293465200&1125984433750&-1435003762500\\
-50293465200&83658415217471&206242965000&-26574143750\\
1125984433750&206242965000&61800032332121&80360210700\\
-1435003762500&-26574143750&80360210700&11170189945871
\end{pmatrix}.
$$

 The four leading principal determinants are 

$$
\begin{aligned}
&206417059721,\\
&17265994657467102998545591,\\
&960941324740480331793743845178086291011,\\
&65442104145157248520714038046591467785805073713081.
\end{aligned}
$$

 All are positive. Sylvester’s criterion and the lower lemma give 

$$
\boxed{\mu(x_1)^2\le\frac{1979}{2000}<\frac{99}{100}<\mu(x_2)^2.}
$$



## Approximation and rational witness

The squared approximations are exactly 

$$
\begin{aligned}
\widetilde\mu(x_1)^2&=\frac{69694107852573439503892031925}{69323394392991282508138323472},\\
\widetilde\mu(x_2)^2&=\frac{5430772101137459612205263871781350}{5387955615790281743396033884265233}.
\end{aligned}
$$

 Cross multiplication yields 

$$
\boxed{\widetilde\mu(x_1)^2<1.006<1.007<\widetilde\mu(x_2)^2,}
$$

 where the decimals are exact rational cutoffs.

The upper completion also has a fully rational form. Put $\omega=w^Tw$, $h=w^Tz$, $c_0=r-w(w^Tr)/\omega$, $a_0=-A^Tw+(h/s)x$. Then 

$$
E=-ww^TA/\omega+c_0x^T/s+\frac{h\,c_0a_0^T}{\omega s\kappa-h^2}.
$$

 The verifier directly checks the perturbed normal equations and positivity of all leading principal minors of $\kappa I-E^TE$. The complete rational matrix is saved in its results file.

A dense variant multiplies $A,b$ by the Hadamard matrix with rows $(1,1,1,1)$, $(1,-1,1,-1)$, $(1,1,-1,-1)$, $(1,-1,-1,1)$, producing 

$$
A'=\begin{pmatrix}1&6&5\\1&-6&5\\1&6&-5\\1&-6&-5\end{pmatrix},\qquad b'=(14,10,10,10)^T.
$$

 This multiplier is twice orthogonal. Iterates are unchanged and both error quantities double, preserving the strict increases without a zero row.

## Sources and scope

Recovered references: OpenProblemsInNLA, provisionally IE-17, *Monotonic optimal backward error along LSMR*; D. C.-L. Fong and M. A. Saunders, *LSMR: An Iterative Algorithm for Sparse Least-Squares Problems*, SIAM J. Sci. Comput. 33(5), 2011, 2950–2971, DOI 10.1137/10079687X.[^IE-17-1] The target addressed here uses the explicit spectral-norm definition in Section 1. The current repository statement was not independently retrieved during reconstruction. A different norm or a perturbation model allowing changes to $b$ is outside this certificate’s stated claim.

[^IE-17-1]: <https://arxiv.org/abs/1006.0758>. Reference metadata was retained from earlier notes; source conventions and priority require verification.


---

# Failure of a pairwise four-step bound for restarted Anderson acceleration

*Reconstructed candidate proof draft. Independent mathematical review and source/priority verification are required. The IE identifiers are provisional labels recovered from earlier notes, not verified current repository identifiers.*

## The finite-step assertion

For symmetric $M$ with $A=I-M$ nonsingular, define 

$$
\alpha(v)=\frac{v^TAv}{v^TA^2v},\qquad R(v)=M[I-\alpha(v)A]v\quad(v\ne0),\qquad R(0)=0.
$$

 The residual after four original steps is $R(R(v))$. For eigenvalues $m_i$, let 

$$
\Lambda(M)=\max_{i<j}\left(\frac{m_im_j(m_j-m_i)}{|m_i(1-m_i)|+|m_j(1-m_j)|}\right)^2.
$$

 For the formula to be defined, each pair considered must have nonzero denominator; all pairs in the examples below do. The target assertion as recovered is $\max_{v\ne0}\left\lVert R(R(v))\right\rVert_2/\left\lVert v\right\rVert_2=\Lambda(M)$. The square is part of the proposed norm amplification; squared-norm comparisons require $\Lambda(M)^2$.

## Exact examples

For $M=\operatorname{diag}(1/10,1/2,3/5)$ and $v=(1,1,1)^T$, direct rational substitution gives 

$$
\alpha(v)=90/61,\quad R(v)=(-2,8,15)^T/61,\quad \alpha(R(v))=3140/1381,
$$

 

$$
R(R(v))=(289,-756,1125)^T/84241,\qquad \Lambda(M)=1/121.
$$

 Consequently 

$$
\frac{\left\lVert R(R(v))\right\rVert_2^2}{\left\lVert v\right\rVert_2^2}=\frac{1920682}{21289638243}>\frac1{14641}=\Lambda(M)^2,
$$

 because $1920682\cdot14641=28120705162>21289638243$. Both $M$ and $I-M$ are positive definite, and $\rho(M)=3/5<1$.

For the simpler semidefinite $M=\operatorname{diag}(0,1/2,2/3)$, 

$$
\alpha(v)=66/49,\quad R(v)=(0,8,18)^T/49,\quad\alpha(R(v))=35/13,
$$

 

$$
R(R(v))=(0,-18,16)^T/637,\qquad\Lambda(M)=4/289.
$$

 Here the squared comparison is $580/1217307>16/83521$, certified by $48442180>19476912$ after cross multiplication. No optimization or tolerance is involved.

## Unbounded underestimation

Let $M_\varepsilon=\operatorname{diag}(\varepsilon^2,1/2,1/2+\varepsilon)$, $v=(1,1,1)^T$, with $0<\varepsilon<1/2$. Both $M_\varepsilon$ and its complement are positive definite. We claim 

$$
\frac{\left\lVert R_\varepsilon(R_\varepsilon(v))\right\rVert_2}{\left\lVert v\right\rVert_2}=\frac{\varepsilon}{6\sqrt6}+O(\varepsilon^2),
\qquad \Lambda(M_\varepsilon)=\frac{\varepsilon^2}{4}+O(\varepsilon^3).
$$

 All intermediate denominators are nonzero at $\varepsilon=0$. Expansion gives 

$$
\alpha_\varepsilon(v)=\tfrac43+\tfrac29\varepsilon+O(\varepsilon^2).
$$

 For $w_\varepsilon=R_\varepsilon(v)$, 

$$
w_0=(0,1/6,1/6)^T,\qquad w'_0=(0,-1/18,17/18)^T.
$$

 With $a(\varepsilon)=(1-\varepsilon^2,1/2,1/2-\varepsilon)$, the second coefficient is 

$$
\beta_\varepsilon=\frac{\sum_i a_iw_{\varepsilon,i}^2}{\sum_i a_i^2w_{\varepsilon,i}^2}=2+2\varepsilon+O(\varepsilon^2).
$$

 Its numerator has value $1/36$ and derivative $13/108$ at zero, and denominator has value $1/72$ and derivative $5/108$. Differentiating the second residual gives 

$$
R_\varepsilon(w_\varepsilon)=\varepsilon(0,-1/12,1/12)^T+O(\varepsilon^2),
$$

 proving the norm expansion. The pair $1/2,1/2+\varepsilon$ contributes 

$$
\left(\frac{\varepsilon(1+2\varepsilon)}{2-4\varepsilon^2}\right)^2=\varepsilon^2/4+O(\varepsilon^3).
$$

 Pairs involving $\varepsilon^2$ contribute $O(\varepsilon^4)$, since their denominators tend to $1/4$. Thus the former pair is maximal for sufficiently small $\varepsilon$, proving the second expansion. Their ratio is 

$$
\boxed{\frac{2}{3\sqrt6}\varepsilon^{-1}+O(1)\longrightarrow\infty.}
$$

 No fixed multiplicative constant repairs the proposed expression as a uniform four-step upper bound on positive-definite contractions.

## Independent recurrence check and limits

The code independently executes two cycles of 

$$
r_1=Mr_0,\quad d=r_1-r_0,\quad\gamma=-r_1^Td/(d^Td),\quad r_2=M(r_1+\gamma d).
$$

 Since $d=-Ar_0$, this gives $r_2=R(r_0)$. The exact vectors and inequalities are checked in both formulations. The continuous-family result is analytic, not established by finite sampling. A large amplification at one residual need not persist on an orbit; the asymptotic-convergence conjecture remains outside these results.

## Sources and scope

Recovered references: OpenProblemsInNLA, provisionally IE-18, *Exact four-step amplification for restarted Anderson acceleration*; O. A. Krzysik, H. De Sterck and A. Smith, *Asymptotic convergence of restarted Anderson acceleration for certain normal linear systems*, SIAM J. Sci. Comput. 47 (2025), DOI 10.1137/24M1672262, arXiv:2312.04776v4, equation (27).[^IE-18-1] The finite-step assertion in Section 1 is the precise mathematical target here. No assertion is made that a different formula, exponent convention, or asymptotic statement in the original paper is refuted without verifying that source.

[^IE-18-1]: <https://arxiv.org/html/2312.04776v4>. Bibliographic details and exact target scope are retained as source leads, not independently verified during reconstruction.


---

# An entrywise inverse-norm conjecture and its sharp replacement

*Reconstructed candidate proof draft. Independent mathematical review and source/priority verification are required. The IE identifiers are provisional labels recovered from earlier notes, not verified current repository identifiers.*

## Counterexample

Let $n\ge3$, $m>0$, $\alpha\ge(n-2)m$, and $S=\alpha I+m\boldsymbol 1\boldsymbol 1^T$. The target as recovered asks whether a symmetric, entrywise positive, diagonally dominant $J\le S$ entrywise must have $\left\lVert J^{-1}\right\rVert_\infty\ge\left\lVert S^{-1}\right\rVert_\infty$.

For $n=3$, $m=\alpha=1$, take 

$$
S=\begin{pmatrix}2&1&1\\1&2&1\\1&1&2\end{pmatrix},\qquad
J=\begin{pmatrix}2&1/2&1/2\\1/2&2&1/2\\1/2&1/2&2\end{pmatrix}.
$$

 All entries of $J$ are positive, $J\le S$ entrywise, and $J$ is strictly diagonally dominant. Yet 

$$
S^{-1}=I-\tfrac14\boldsymbol 1\boldsymbol 1^T,\quad J^{-1}=\tfrac23I-\tfrac19\boldsymbol 1\boldsymbol 1^T,
\qquad\boxed{\left\lVert J^{-1}\right\rVert_\infty=\tfrac79<\tfrac54=\left\lVert S^{-1}\right\rVert_\infty.}
$$



## Sharp infimum

**Theorem 1**. *For every admissible $n,m,\alpha$, over the stated class, 

$$
\boxed{\inf_J\left\lVert J^{-1}\right\rVert_\infty=\frac1{\alpha+m}.}
$$

 Strict positivity of all entries prevents attainment.*

*Proof.* All such $J$ are positive definite, because 

$$
x^TJx=\sum_i\left(J_{ii}-\sum_{j\ne i}J_{ij}\right)x_i^2
+\sum_{i<j}J_{ij}(x_i+x_j)^2.
$$

 Every term is nonnegative, and for $n\ge3$, vanishing of all $x_i+x_j$ forces $x=0$. Cauchy–Schwarz applied to $J^{1/2}e_i,J^{-1/2}e_i$ gives $J_{ii}(J^{-1})_{ii}\ge1$. Equality would require $e_i$ to be an eigenvector, impossible with positive off-diagonal entries. With $D=\alpha+m$, 

$$
\left\lVert J^{-1}\right\rVert_\infty\ge(J^{-1})_{ii}>1/J_{ii}\ge1/D.
$$

 For $0<\varepsilon\le m$, let $J_\varepsilon=(D-\varepsilon)I+\varepsilon\boldsymbol 1\boldsymbol 1^T$. Its diagonal is $D$, its off-diagonal entries are $\varepsilon$, and $D\ge(n-1)m\ge(n-1)\varepsilon$, so it belongs to the class. Direct inversion yields 

$$
\left\lVert J_\varepsilon^{-1}\right\rVert_\infty=
\frac{D+(2n-3)\varepsilon}{(D-\varepsilon)(D+(n-1)\varepsilon)}\longrightarrow\frac1D.
$$

 This proves both the value and nonattainment. ◻

The gap between the proposed value and the actual infimum is 

$$
\left\lVert S^{-1}\right\rVert_\infty-\frac1{\alpha+m}
=\frac{(n-1)m(\alpha+2m)}{\alpha(\alpha+m)(\alpha+nm)}>0.
$$



## Scope, checks, and sources

The exact verifier checks both inverses and the class assumptions, and tests the parameterized inverse formula at rational parameters. The universal lower bound and limiting claim are analytic arguments. A stronger ordering involving dominance margins is a different question; this example is not claimed to satisfy it.

Recovered references: OpenProblemsInNLA, provisionally IE-19, *Sharp inverse norm bound from upper bounds on matrix entries*; originating preprint arXiv:1203.6812, Conjecture 8.1.[^IE-19-1] The current repository statement was not retrieved. The result concerns the explicit formulation in Section 1 and must not be attributed to a different formulation without checking the source.

[^IE-19-1]: <https://arxiv.org/abs/1203.6812>. Bibliographic details and original-source conventions are recovered reference leads, not independently verified here.


---

# Sharp Gaussian constants for row deletion in unit-row matrices

*Reconstructed candidate proof draft. Independent mathematical review and source/priority verification are required. The IE identifiers are provisional labels recovered from earlier notes, not verified current repository identifiers.*

## Definitions and statements

Fix $0<\theta<1$, let $A\in\mathbb R^{m\times n}$ have unit Euclidean row norms, and set $k=\lfloor\theta m\rfloor$. Define 

$$
s_\theta(A)=\min_{|S|=k}\sigma_{\min}(A_S)
=\min_{\left\lVert x\right\rVert_2=1}\left(\sum_{i=1}^k(|Ax|^2)_{(i)}\right)^{1/2},
$$

 where order is increasing, $\sigma_{\min}$ denotes the variational minimum over unit vectors (zero for a rank-deficient map), and empty sums are zero. The equality follows by interchanging the finite and compact minima.

Let $G\sim N(0,1)$, $\mathbb P(|G|\le a_\theta)=\theta$, and let $\varphi$ be its density. Set 

$$
h_\theta=\mathbb E[G^2\mathbf1_{|G|\le a_\theta}]=\theta-2a_\theta\varphi(a_\theta),\qquad c_\theta=\sqrt{h_\theta}.
$$



**Theorem 1** (Random rows). *For independent uniform rows on $S^{n-1}$, along every sequence $n\to\infty$, $m/n\to\infty$, in probability 

$$
\frac nm s_\theta(A)^2\to h_\theta,\qquad \frac nm\left\lVert A\right\rVert_2^2\to1,\qquad
\frac{s_\theta(A)^2}{\left\lVert A\right\rVert_2^2}\to h_\theta.
$$

*

**Theorem 2** (Universal constant). *Uniformly in all integers $m\ge1$ and unit-row matrices $A\in\mathbb R^{m\times n}$, 

$$
\sqrt{n/m}\,s_\theta(A)\le c_\theta+o_{n\to\infty}(1).
$$

 No smaller constant has the eventual uniform upper-bound property. Along every $n\to\infty$, $m/n\to\infty$, the supremum over unit-row matrices of $\sqrt{n/m}\,s_\theta(A)$ converges to $c_\theta$.*

## Trimming identities

For nonnegative $y_1,\ldots,y_m$, 

$$
\frac1m\sum_{i=1}^k y_{(i)}=\max_{t\ge0}\left\{\frac km t-\frac1m\sum_i(t-y_i)_+\right\}.
$$

 The right side is concave piecewise linear, with slope $k/m$ minus the empirical distribution function, and is maximized between the $k$th and $(k+1)$st order statistics; use $t=0$ for $k=0$.

For a nonnegative random variable $Y$, define 

$$
H_\theta(Y)=\inf\{\mathbb E(Yw):0\le w\le1,\ \mathbb Ew=\theta\}.
$$

 This is the integral of the lower quantiles through mass $\theta$. For a continuous distribution it is $\mathbb E[Y\mathbf1_{Y\le b_\theta}]$. Under any coupling of $Y,Z$, 

$$
|H_\theta(Y)-H_\theta(Z)|\le\mathbb E|Y-Z|.
$$

 Indeed use the same feasible selectors on the joint space. Allowing selectors to depend on both variables does not change either infimum: conditional expectation given one variable preserves the constraints.

## Pointwise concentration

Let $u$ be uniform on $S^{n-1}$, $n\ge2$, $Y_n=nu_1^2$, and $h_{\theta,n}=H_\theta(Y_n)$. Its law is continuous and its mean is one. Put $L=2/(1-\theta)$. For independent copies $Y_i$, $T_m=m^{-1}\sum_{i=1}^kY_{(i)}$, and $0<\epsilon\le(1-\theta)/2$, we claim 

$$
\mathbb P\bigl(|T_m-h_{\theta,n}|>2L\epsilon+L/m\bigr)\le5e^{-2m\epsilon^2}.
$$

 Let $b$ be the $\theta$-quantile. Since the mean is one, $b\le1/(1-\theta)\le L$. Hoeffding’s bounded-variable inequality gives, outside total probability $4e^{-2m\epsilon^2}$, 

$$
\left|m^{-1}\sum_i\mathbf1_{Y_i\le b}-\theta\right|\le\epsilon,\qquad
\left|m^{-1}\sum_iY_i\mathbf1_{Y_i\le b}-h_{\theta,n}\right|\le b\epsilon.
$$

 Markov’s inequality gives $\mathbb P(Y_n\le L)\ge(1+\theta)/2$. The chance fewer than $k$ samples are at most $L$ is at most $e^{-m(1-\theta)^2/2}\le e^{-2m\epsilon^2}$. On the complementary events, replacing the sum below $b$ by the $k$ smallest terms changes at most $m\epsilon+1$ terms, each at most $L$. This proves the claim. For $k=0$, use $h_{\theta,n}\le\theta<1/m$.

The bounded-variable inequality used here follows from $\mathbb Ee^{\lambda(X-\mathbb EX)}\le e^{\lambda^2b^2/8}$ for $0\le X\le b$, independence, and optimization of the Chernoff parameter. The scalar exponential bound follows by convexity on an interval and a one-variable maximization.

## Covariance and uniform directions

The moments satisfy 

$$
\mathbb EY_n^r=\frac{n^r(2r-1)!!}{n(n+2)\cdots(n+2r-2)}\le2^r r!,
$$

 so $\mathbb E|Y_n-1|^r\le4^r r!$ and, for $|\lambda|\le1/8$, $\mathbb Ee^{\lambda(Y_n-1)}\le e^{32\lambda^2}$. The mean-zero linear term vanishes; summing the remaining geometric series gives this bound. Chernoff’s inequality then yields, for $0<u\le1$, 

$$
\mathbb P\left(\left|m^{-1}\sum_iY_i-1\right|>u\right)\le2e^{-mu^2/128}.
$$

 A $1/4$-net of the real unit sphere has at most $9^n$ points; a symmetric matrix’s norm is at most twice its maximum absolute quadratic form on that net. For $C=(n/m)A^TA$ this gives 

$$
\mathbb P(\left\lVert C-I\right\rVert_2>t)\le2\,9^n e^{-mt^2/512}\quad(0<t\le1).
$$

 The net cardinality follows by disjoint-ball volume comparison; the quadratic-form estimate follows by approximating a maximizing unit vector.

Let $T(x)=(n/m)\min_{|S|=k}\left\lVert A_Sx\right\rVert_2^2$. On $\left\lVert C-I\right\rVert_2\le t$, every submatrix quadratic form has norm at most $1+t$, hence 

$$
|T(x)-T(y)|\le2(1+t)\left\lVert x-y\right\rVert_2
$$

 for unit $x,y$. A $\delta$-net has at most $(1+2/\delta)^n$ points. Pointwise concentration, a union bound, and this Lipschitz estimate give 

$$
\sup_{\left\lVert x\right\rVert_2=1}|T(x)-h_{\theta,n}|\le D:=2L\epsilon+L/m+2(1+t)\delta
$$

 except with probability 

$$
2\,9^n e^{-mt^2/512}+5(1+2/\delta)^n e^{-2m\epsilon^2},
$$

 where $0<t<1$, $0<\delta<1$, $0<\epsilon\le(1-\theta)/2$.

## Gaussian limit and explicit random error

Couple $u$ with an independent radius $R^2\sim\chi_n^2$. Then $Ru$ is standard Gaussian, so $G_1^2=(R^2/n)Y_n$. Independence and the chi-square variance give 

$$
\mathbb E|Y_n-G_1^2|=\mathbb E|1-R^2/n|\le\sqrt{2/n},\qquad
|h_{\theta,n}-h_\theta|\le\sqrt{2/n}.
$$

 With the preceding exceptional probability, 

$$
\left|\frac nm s_\theta(A)^2-h_\theta\right|\le D+\sqrt{2/n},
$$

 

$$
\left|\frac{s_\theta(A)^2}{\left\lVert A\right\rVert_2^2}-h_\theta\right|
\le\frac{D+\sqrt{2/n}+t}{1-t}.
$$

 Here $h_\theta\le1$. If $Q=m/n\to\infty$, eventually choose $t=\epsilon=\delta=32\sqrt{\log Q/Q}$. Parameter restrictions eventually hold; both failure probabilities vanish and the error is 

$$
O_\theta\left(\sqrt{\frac nm\log\frac mn}+n^{-1/2}+m^{-1}\right).
$$

 No additional condition on how quickly $Q$ diverges is needed. This proves the random theorem.

## Deterministic projection argument

For arbitrary unit-row $A$, choose $1\le r<n$, set $d=n-r$, and remove the $r$ largest covariance eigenvector directions. In orthonormal coordinates on the remaining subspace, call the projected matrix $B\in\mathbb R^{m\times d}$. Since $\operatorname{tr}(A^TA)=m$, 

$$
\left\lVert B\right\rVert_2^2\le m/(r+1),\qquad\left\lVert b_i\right\rVert_2\le1,\qquad\operatorname{tr}(B^TB)\le m.
$$

 Let $g\sim N(0,I_d)$ and $Y_i=(b_i^Tg)^2$; these variables may be correlated. Define 

$$
\Psi_t(g)=\frac km t-\frac1m\sum_i(t-Y_i)_+.
$$

 Each scalar Gaussian $b_i^Tg$ has variance at most one, so 

$$
\mathbb E\Psi_t(g)\le\theta t-\mathbb E(t-G^2)_+\le h_\theta.
$$

 The final inequality is the population trimming formula, maximized at $t=a_\theta^2$.

Gaussian Poincaré gives $\operatorname{Var}(f(g))\le\mathbb E\left\lVert\nabla f(g)\right\rVert_2^2$. A proof expands smooth functions in tensor Hermite polynomials: variance sums squared nonconstant coefficients, while the gradient norm weights them by total degree, at least one. Smooth approximation extends the inequality to Lipschitz functions. Since the scalar derivative of $(t-z^2)_+$ is bounded by $2\sqrt t$, 

$$
\operatorname{Var}(\Psi_t(g))\le\frac{\left\lVert B\right\rVert_2^2}{m^2}(4tm)\le\frac{4t}{r+1}.
$$

 This handles arbitrary row correlations without asserting independence.

## Explicit uniform bound and sharpness

For $0<\delta<1$, a grid of $[0,L]$ with spacing at most $\delta$ has at most $L/\delta+2$ points. Chebyshev’s inequality and the last variance bound show that all grid values obey $\Psi_t\le h_\theta+\delta$, except with probability at most 

$$
\frac{4L(L/\delta+2)}{(r+1)\delta^2}.
$$

 Since $t\mapsto\Psi_t$ is 1-Lipschitz, its supremum on $[0,L]$ is at most $h_\theta+2\delta$ on that event’s complement.

Also $Z=m^{-1}\left\lVert Bg\right\rVert_2^2$ has mean at most one and variance $2\operatorname{tr}((B^TB)^2)/m^2\le2/(r+1)$. Thus $Z\le2$ except with probability $2/(r+1)$. On that event, the $k$th order statistic is at most $L$, because at least $m-k+1\ge(1-\theta)m$ terms are as large. Therefore the full trimming maximum is attained in $[0,L]$; the case $k=0$ is immediate.

Finally, $\mathbb P(\left\lVert g\right\rVert_2^2<(1-\delta)d)\le2/(d\delta^2)$. Consequently, if 

$$
\frac2{r+1}+\frac{4L(L/\delta+2)}{(r+1)\delta^2}
+\frac2{(n-r)\delta^2}<1,
$$

 there exists a realization satisfying all the bounds. Normalize that $g$ to a unit direction in the retained subspace. The trimming identity yields 

$$
\boxed{\frac nm s_\theta(A)^2\le\frac{n}{(n-r)(1-\delta)}(h_\theta+2\delta).}
$$

 All constants are independent of $m,A$. Taking $r=\lfloor n^{2/3}\rfloor$, $\delta=n^{-1/6}$ makes the condition hold for all sufficiently large $n$ for fixed $\theta$; its largest term is $O_\theta(n^{-1/6})$. The result is the uniform bound $(n/m)s_\theta(A)^2\le h_\theta+O_\theta(n^{-1/6})$.

The random theorem supplies deterministic realizations arbitrarily close to $h_\theta$ along every high-aspect-ratio sequence. Thus no smaller constant can satisfy the eventual uniform requirement, and the normalized supremum converges to $c_\theta$. This proves the second theorem’s two quantifier claims without interchanging an unjustified random minimum and expectation.

## Sources and verification limits

Recovered target descriptions: *Sharp row-deletion constant for spherical random matrices*, provisionally IE-21, and *Optimal uniform row-deletion constant*, provisionally IE-22, in OpenProblemsInNLA.[^IE-21-22-1] Earlier conversational summaries assigned different identifiers to these topics; the present labels are local identifiers only until the repository mapping is checked.

The live source statements could not be retrieved during reconstruction. The precise normalization, retention convention, singular-value definition, and quantifiers in Section 1 are essential. The probability and existence arguments need independent mathematical review; finite tests of the other notes do not certify them.

[^IE-21-22-1]: <https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/linear-systems-and-elimination>.


---

# Nonuniqueness of induced-norm-minimizing right inverses

*Reconstructed candidate proof draft. Independent mathematical review and source/priority verification are required. The IE identifiers are provisional labels recovered from earlier notes, not verified current repository identifiers.*

## Pointwise orthogonality

For full-row-rank $A\in\mathbb C^{m\times n}$, $m<n$, consider 

$$
\min_{AY=I_m}\left\lVert Y\right\rVert_{p\to2},\qquad \left\lVert Y\right\rVert_{p\to2}=\sup_{z\ne0}\left\lVert Yz\right\rVert_2/\left\lVert z\right\rVert_p.
$$

 If $B=A^\dagger$, every right inverse is $Y=B+N$ with $AN=0$. Since $B=A^*(AA^*)^{-1}$, $B^*N=0$, and therefore 

$$
\left\lVert Yz\right\rVert_2^2=\left\lVert Bz\right\rVert_2^2+\left\lVert Nz\right\rVert_2^2.
$$

 Thus $B$ minimizes the objective for every $p$. This is not the different product objective $\left\lVert YA\right\rVert_{p\to2}$.

## Smallest counterexample

**Theorem 1**. *Let 

$$
A=\begin{pmatrix}1&1&0\\1&0&1\end{pmatrix},\quad
B=\tfrac13\begin{pmatrix}1&1\\2&-1\\-1&2\end{pmatrix},\quad
X=\begin{pmatrix}0&0\\1&0\\0&1\end{pmatrix}.
$$

 Then $B=A^\dagger$, $AB=AX=I_2$, $B\ne X$, and for $2\le p\le\infty$, 

$$
\boxed{\left\lVert B\right\rVert_{p\to2}=\left\lVert X\right\rVert_{p\to2}=\min_{AY=I_2}\left\lVert Y\right\rVert_{p\to2}=2^{1/2-1/p}.}
$$

*

*Proof.* Direct multiplication gives $B^*B=\tfrac13\left(\begin{smallmatrix}2&-1\\-1&2\end{smallmatrix}\right)\preceq I_2$ and $X^*X=I_2$. The inequality $\left\lVert z\right\rVert_2\le2^{1/2-1/p}\left\lVert z\right\rVert_p$ gives both upper bounds. At $z=(1,-1)^T$ both matrices preserve Euclidean norm, so the bounds are attained. Pointwise orthogonality proves global optimality. ◻

When $m=1$, the right inverse is a single column, and its induced norm is its Euclidean norm for all $p$; orthogonality makes the minimum unique. Hence dimensions $2\times3$ are smallest.

## Complete minimizer set

Every right inverse is $B+v(a,b)$, where $v=(-1,1,1)^T$. At norming vector $(1,-1)^T$, orthogonality forces $a=b=t$ for any minimizer. The Gram matrix of $Y=B+t v(1,1)$ has eigenvalue one on $(1,-1)^T$ and eigenvalue $1/3+6|t|^2$ on $(1,1)^T$. Both vectors have equal-modulus coordinates. Testing the latter forces $|t|\le1/3$. Conversely this condition gives $Y^*Y\preceq I_2$ and the same attained bound. Thus for every $2\le p\le\infty$, all minimizers are 

$$
\boxed{B+t(-1,1,1)^T(1,1),\qquad |t|\le\tfrac13.}
$$

 The real parameter interval is $[-1/3,1/3]$, and $X$ corresponds to $t=1/3$.

## Every complex dimension

For $2\le m<n$, take $A=(\boldsymbol 1\ \ I_m\ \ 0_{m\times(n-m-1)})$, $B=A^\dagger$. Then 

$$
B^*B=I_m-\frac{\boldsymbol 1\boldsymbol 1^*}{m+1}\preceq I_m.
$$

 The $m-1$ nonconstant Fourier vectors $(1,\omega^j,\ldots,\omega^{(m-1)j})^T$, $1\le j<m$, $\omega=e^{2\pi i/m}$, have flat coordinate moduli and span $\boldsymbol 1^\perp$. The matrix $B$ preserves their Euclidean norms. Together with $\left\lVert z\right\rVert_2\le m^{1/2-1/p}\left\lVert z\right\rVert_p$, this proves optimum $m^{1/2-1/p}$ and makes those vectors norming vectors.

For an optimal $Y=B+N$, orthogonality forces $N$ to vanish on every Fourier vector, hence on $\boldsymbol 1^\perp$. Therefore $N=u\boldsymbol 1^*$ with $u\in\ker A$. Its Gram matrix is 

$$
Y^*Y=I_m+\left(\left\lVert u\right\rVert_2^2-\frac1{m+1}\right)\boldsymbol 1\boldsymbol 1^*.
$$

 Testing the flat vector $\boldsymbol 1$ shows that $\left\lVert u\right\rVert_2\le(m+1)^{-1/2}$ is necessary, and $Y^*Y\preceq I_m$ shows sufficiency. Thus the complete complex minimizer set is 

$$
\boxed{B+u\boldsymbol 1^*,\quad u\in\ker A,\quad \left\lVert u\right\rVert_2\le(m+1)^{-1/2}.}
$$

 This higher-dimensional statement uses complex Fourier vectors. The smallest counterexample is valid over either field.

## Attribution and verification

The rational verifier checks the right-inverse, Gram, and kernel identities. Continuous parameter ranges and complete minimizer sets are analytic claims. The recovered notes attribute the smallest $A,B$ to Example 4.1 of Dokmanić and Gribonval for the spectral norm; that construction is not claimed as new, and the attribution should be checked before publication.

Recovered references: OpenProblemsInNLA, provisionally IE-23; I. Dokmanić and R. Gribonval, *Beyond Moore–Penrose, Part I: Generalized Inverses that Minimize Matrix Norms*, arXiv:1706.08349v2 (2017), Example 4.1, Corollary 4.2(3), Remark 4.1.[^IE-23-1] The live repository statement was not independently retrieved during reconstruction.

[^IE-23-1]: <https://arxiv.org/abs/1706.08349>. References retained as source leads; priority and exact source scope require checking.
