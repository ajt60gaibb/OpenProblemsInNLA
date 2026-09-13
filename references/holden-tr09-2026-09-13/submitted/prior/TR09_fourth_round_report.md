# TR-09: mixed-block cancellation and a coherence-dependent local barrier

## Result and scope

This note does **not** establish a full solution of TR-09. It continues the staged-ALS investigation with two self-contained local results. First, at a decomposition with two orthogonal factor modes, an explicit cycle of genuine mixed-factor least-squares updates annihilates the entire first-order tensor error. The third factor mode can be arbitrarily coherent, provided its columns are nonzero and pairwise noncollinear. In an identifiable local coordinate chart, this gives quadratic convergence.

Second, when all three modes are coherent, a rank-two example gives an explicit lower bound on the number of these least-squares blocks needed for a constant local residual reduction. The bound holds even when the blocks are chosen adaptively. It diverges as the two components approach collinearity.

Neither result supplies the missing global, randomly initialized, once-smoothed guarantee for arbitrary deterministic base matrices. The local theorem has a geometry-dependent neighborhood; the lower bound covers a specified width-two block class rather than every algorithm and width allowed by TR-09. No independent review, formal verification, or literature-wide novelty claim is made.

## 1. The target inherited from the previous report

The canonical question concerns a tensor generated from arbitrary deterministic factor bases followed by one independent Gaussian perturbation of their entries. It asks for an admissible optimization procedure with width

\[
 k(r)=o(r^2),
\]

an input-independent random initializer, arbitrary relative Frobenius accuracy, and a polynomial exact-real operation bound in the dimension, rank, and logarithm of inverse accuracy. The high-probability statement over smoothing must precede the conditional initialization-success statement. Computing a decomposition by another method and merely calling it an optimization initializer does not establish that target. [1,2]

The preceding staged-ALS report claims an in-target positive result for a near-orthogonal family and its once-smoothed orthogonal-base subclass, including unrestricted component-weight ratios. Its remaining scope is arbitrary base coherence. Its proof and experiments are not independently verified by this note. The present results investigate that remaining geometry; they do not extend the earlier smoothing theorem to arbitrary bases. [2]

All mathematical assertions below are proved within this note. The sources at the end identify the target and the preceding work, not external premises for the local theorems.

## 2. Genuine mixed-factor least squares

Write

\[
 \mathcal S(A,B,C)=\sum_{i=1}^r a_i\otimes b_i\otimes c_i,
 \qquad F_T(A,B,C)=\|\mathcal S(A,B,C)-T\|_F^2.
\]

For every component, select either one of its three factor vectors or no vector. Freeze all other variables. Because at most one factor of each summand is free, the represented tensor is affine linear in the collection of selected variables. Vectorizing gives a least-squares problem

\[
 \min_z\|D z+f-\operatorname{vec}(T)\|_2^2.
\]

Whenever the design has full column rank, its unique solution is

\[
 z^+=(D^\top D)^{-1}D^\top(\operatorname{vec}(T)-f). \tag{2.1}
\]

Selecting first-mode vectors from some components and second- or third-mode vectors from others does not introduce bilinear unknowns: the selected variables belong to different summands. Each update is an actual minimizer of the original objective over its stated block. No tensor transformation or factor initialization is concealed in this definition.

This note makes no claim to invent the general methodology of mixed-factor least squares. Its mathematical objects are the explicit schedule and results below. Whether a particular repository convention uses “ALS” narrowly for single-mode blocks does not affect the proofs; in either interpretation these local results alone do not solve its global problem.

### 2.1 The local projection identity

Let \(\theta_*\) be an exact factorization, let \(J\) be the derivative of \(\mathcal S\) there, and let \(D_*\) be the selected block's design at that factorization. Suppose \(D_*\) is full column rank. The first-order tensor error after the exact block update is

\[
 (I-P_{D_*})J h,
 \qquad P_{D_*}=D_*(D_*^\top D_*)^{-1}D_*^\top, \tag{2.2}
\]

when the incoming factor perturbation is \(h\).

To prove this, differentiate the block normal equations \(D^\top E^+=0\), where \(E=\mathcal S-T\). At an exact fit the residual is zero, so the derivative of \(D^\top\) contributes no term. The block correction solves the linearized least-squares problem against \(Jh\), giving (2.2). This argument accounts for the dependence of the design on the frozen factors; it does not freeze that dependence incorrectly.

## 3. A logarithmic-length schedule with zero local derivative

Assume \(n\ge r\ge2\), and consider

\[
 T=\sum_{i=1}^r a_i\otimes b_i\otimes c_i,\qquad
 B^\top B=C^\top C=I_r. \tag{3.1}
\]

The first-mode columns \(a_i\) are nonzero and every pair \(a_i,a_j\), \(i\ne j\), is linearly independent. The matrix \(A\) itself need not have full column rank. There is no bound on its column norms or on its pairwise correlations away from one.

Assign each component its distinct binary code \(i-1\), using \(m=\lceil\log_2 r\rceil\) bits. A cycle consists of:

1. One full first-mode least-squares update of all \(a_i\).
2. For each bit, a mixed block choosing \(b_i\) for components whose bit is zero and \(c_i\) for components whose bit is one.
3. Immediately after that block, its complementary choice, choosing \(c_i\) on the zero side and \(b_i\) on the one side.

The cycle has \(1+2\lceil\log_2 r\rceil\) blocks. For rank one, use one ordinary first/second/third-mode sweep instead.

### Theorem 3.1: exact first-order cancellation

At every factorization satisfying (3.1), all block designs in this cycle are full column rank. The derivative of the represented tensor after one cycle annihilates every incoming factor perturbation:

\[
 (I-P_q)\cdots(I-P_1)J=0,\qquad q=1+2\lceil\log_2 r\rceil. \tag{3.2}
\]

In local coordinates that remove the usual component scaling freedom, the derivative of the complete cycle itself is zero.

### Proof

Orthogonal changes of coordinates in the second and third modes allow us to take \(b_i=c_i=e_i\). These changes are used only to prove the theorem; the algorithm need not know or compute them.

A first-order tensor perturbation is

\[
 E=\sum_i\Delta a_i\otimes e_i\otimes e_i
 +\sum_i a_i\otimes\Delta b_i\otimes e_i
 +\sum_i a_i\otimes e_i\otimes\Delta c_i. \tag{3.3}
\]

Regard a tensor as a matrix of first-mode vector-valued cells indexed by its second- and third-mode coordinates. At an off-diagonal cell \((j,i)\), with \(i,j\le r\) and \(i\ne j\), the error has the form

\[
 E_{j,i}=a_i\beta_{j,i}+a_j\gamma_{i,j}. \tag{3.4}
\]

The coefficient \(\beta_{j,i}\) belongs to the free coordinate of \(b_i\), and \(\gamma_{i,j}\) belongs to the free coordinate of \(c_j\). Cells outside the selected coordinate range contain at most one such direction. Diagonal cells contain arbitrary first-mode vector errors.

The full first-mode block spans all diagonal cells and none of the other cells. Its design is injective and its projection removes every diagonal error.

Consider now a mixed second/third-mode block. Each coordinate of a selected vector contributes in a single cell. Thus the block space is an orthogonal direct sum over cells. An off-diagonal cell contains zero, one, or both of the directions \(a_i,a_j\), according to the selected vectors. When both occur, the corresponding two scalar unknowns are independent because \(a_i,a_j\) are noncollinear. A diagonal or exterior cell contains a nonzero multiple of a single \(a_i\). It follows that every such mixed block design is injective.

For any ordered distinct pair \((i,j)\), their binary codes differ in some bit. One of that bit's two complementary blocks selects both \(b_i\) and \(c_j\). At that block, the entire error (3.4) is projected out. It cannot be recreated by later first-order updates, because every later block projection preserves the decomposition into cells. Each exterior cell is similarly eliminated by a block that selects its contributing vector. The diagonal cells, already zero, remain zero.

Every cell of (3.3) has therefore been eliminated by the end of the cycle, proving (3.2).

It remains to distinguish tensor cancellation from a statement about factor coordinates. Near the true factorization, use the virtual normalization

\[
 \widetilde b_i=\frac{b_i}{\langle b_i^*,b_i\rangle},\quad
 \widetilde c_i=\frac{c_i}{\langle c_i^*,c_i\rangle},\quad
 \widetilde a_i=\langle b_i^*,b_i\rangle\langle c_i^*,c_i\rangle a_i. \tag{3.5}
\]

This does not change any represented term. In this coordinate chart, the second- and third-mode perturbations have zero own-coordinate entries. The derivative \(J\) is injective: diagonal cells determine \(\Delta a_i\); each internal off-diagonal cell determines its two coefficients by pairwise noncollinearity; and exterior cells determine their one coefficient. Therefore (3.2) implies that the derivative of the gauge-normalized factor map is zero.

The normalization is analysis-only. Exact least-squares updates are equivariant under nonzero component rescalings that preserve the represented term, because such a rescaling is an invertible linear change of the selected unknowns. No normalization or data-dependent factor replacement is added to the actual algorithm. This completes the proof.

## 4. Quadratic convergence, and the constants it does not control

### Corollary 4.1: local quadratic convergence

For each fixed factorization satisfying Theorem 3.1, there are constants \(C>0\) and \(d>0\) such that the gauge-normalized error \(e\), whenever \(\|e\|\le d\), obeys

\[
 \|e^+\|\le C\|e\|^2. \tag{4.1}
\]

The neighborhood can be chosen invariant, and the represented tensors converge to \(T\). In that fixed neighborhood, the asymptotic number of cycles for accuracy \(\varepsilon\) is \(O(\log\log(1/\varepsilon))\), with data-dependent constants.

### Proof

Every block Gram matrix is positive definite at the root. By continuity, all are nonsingular in a sufficiently small neighborhood of the finite cycle. Formula (2.1) is rational in the factor entries there and hence analytic. The virtual gauge (3.5) is analytic there as well. The cycle fixes the root and has zero first derivative by Theorem 3.1. Taylor's theorem on a smaller closed neighborhood gives (4.1).

Choose \(d\) additionally so that \(Cd\le1/2\). If \(q_t=C\|e_t\|\), then \(q_{t+1}\le q_t^2\), and consequently

\[
 \|e_t\|\le C^{-1}(C\|e_0\|)^{2^t}\le C^{-1}2^{-2^t}. \tag{4.2}
\]

The tensor map is locally Lipschitz, so its residual satisfies the corresponding bound with a finite multiplicative constant. This proves the convergence claim.

### 4.1 Contrast with ordinary full-mode ALS

For cell (3.4), an ordinary full second-mode update removes only the projection on \(a_i\); the following full third-mode update removes only the projection on \(a_j\). On the corresponding nonzero one-dimensional error coordinate, the cycle multiplier is

\[
 \frac{\langle a_i,a_j\rangle^2}{\|a_i\|^2\|a_j\|^2}. \tag{4.3}
\]

Indeed the two scalar updates are

\[
 \beta^+=-\frac{\langle a_i,a_j\rangle}{\|a_i\|^2}\gamma,
 \qquad
 \gamma^+=-\frac{\langle a_j,a_i\rangle}{\|a_j\|^2}\beta^+.
\]

The multiplier approaches one for nearly parallel columns. The mixed block instead solves both coefficients together, producing zero at first order. This is an exact local distinction, not a numerical comparison.

### 4.2 Why zero derivative is not the TR-09 theorem

Neither \(C\) nor the radius \(d\) above is bounded uniformly over arbitrarily coherent first-mode columns. The inverse Gram matrices contain small pair-separation parameters. The theorem does not show that an input-independent random start lands in the neighborhood with inverse-polynomial probability.

Also, Gaussian smoothing of orthogonal second- and third-mode bases does not preserve their exact orthogonality. Continuity gives a small perturbation neighborhood for each fixed well-defined root, but its size can depend on the first-mode coherence. Arbitrarily large and nearly parallel base columns prevent replacing that pointwise statement by a dimension threshold depending only on rank. Consequently, neither an initialization guarantee nor the required uniform smoothing guarantee follows from Theorem 3.1.

### 4.3 Arithmetic cost

A mixed block selects at most \(nr\) scalar variables. Its normal matrix can be assembled using tensor contractions and factor inner products. Same-mode cross blocks are scalar multiples of the identity; different-mode cross blocks are scaled outer products. A conservative structured cost is

\[
 O(n^3r+n^2r^2+n^3r^3)
\]

per block, using a dense solve of size at most \(nr\). Thus each finite cycle has polynomial exact-real arithmetic cost. A polynomial cost per cycle does not replace the missing uniform bound on reaching its convergence neighborhood. The numerical reference uses a scaled full-rank least-squares solve and records numerical singularity separately.

## 5. A fully coherent rank-two obstruction for the same block class

Let \(0<c<1\), let \(s=\sqrt{1-c^2}\), and put

\[
 u=e_1,\qquad v=ce_1+se_2,\qquad T_c=u^{\otimes3}+v^{\otimes3}. \tag{5.1}
\]

The target has rank two and can be embedded in a larger ambient dimension. At its displayed exact factorization, consider any block that selects at most one complete factor vector from each of the two components. This includes full single-mode blocks, mixed-mode blocks, and their one-component subblocks.

Let \(P\) be the orthogonal projection onto such a block's tangent space and set

\[
 H=e_2^{\otimes3},\qquad \|H\|_F=1,
 \qquad \eta^2=\frac{s^2}{1+c^2}. \tag{5.2}
\]

### Lemma 5.1: an almost-invariant tensor direction

For all these blocks,

\[
 \|PH\|_F^2\le\eta^2. \tag{5.3}
\]

For a two-component block selecting the same mode in both components, equality holds. For a block selecting different modes, the exact value is \(s^4\).

### Proof

For a same-mode block, permute modes to select the first mode. Its range is

\[
 \mathbb R^2\otimes\operatorname{span}\{u\otimes u,v\otimes v\}.
\]

The two-vector Gram matrix and the inner products with \(e_2\otimes e_2\) are

\[
 G=\begin{pmatrix}1&c^2\\c^2&1\end{pmatrix},
 \qquad h=\begin{pmatrix}0\\s^2\end{pmatrix}.
\]

Hence the squared projection norm is

\[
 h^\top G^{-1}h=\frac{s^4}{1-c^4}=\frac{s^2}{1+c^2}. \tag{5.4}
\]

For a mixed block, it suffices by symmetry to select the first vector of component one and the second vector of component two. The two subspaces are

\[
 \mathbb R^2\otimes u\otimes u,
 \qquad v\otimes\mathbb R^2\otimes v.
\]

Their diagonal Gram blocks are \(I_2\); their cross block is \(cvu^\top\). The inner-product vector of \(H\) with the first subspace is zero and with the second is \(s^2e_2\). Since \(u^\top e_2=0\), the cross block annihilates that latter vector. Its squared projection norm is therefore exactly \(s^4\). Finally \(s^4\le s^2/(1+c^2)\). A subblock has a smaller projection norm than a containing block. The same computations remain valid under zero-padding into a larger dimension.

### Theorem 5.2: an adaptive finite-block lower bound

Start the linearized residual at \(R_0=H\), and allow any adaptive choice of the preceding block projections:

\[
 R_t=(I-P_t)R_{t-1},\qquad t=1,\ldots,M.
\]

Then

\[
 \|R_M\|_F\ge
 \max\left\{0,\frac{1-M\eta^2}{1+M\eta^2}\right\}. \tag{5.5}
\]

In particular, reducing the norm to at most one half requires

\[
 M\ge\frac{1+c^2}{3(1-c^2)}. \tag{5.6}
\]

### Proof

Orthogonal projection gives the exact energy identity

\[
 \sum_{t=1}^M\|P_tR_{t-1}\|_F^2=1-\|R_M\|_F^2. \tag{5.7}
\]

Telescoping and Lemma 5.1 imply

\[
 \begin{aligned}
 1-\langle H,R_M\rangle
 &=\sum_{t=1}^M\langle P_tH,P_tR_{t-1}\rangle\\
 &\le\sqrt{M\eta^2}\sqrt{1-\|R_M\|_F^2}.
 \end{aligned} \tag{5.8}
\]

Write \(z=\|R_M\|_F\le1\) and use \(\langle H,R_M\rangle\le z\). For \(z<1\), squaring and canceling \(1-z\) gives

\[
 1-z\le M\eta^2(1+z).
\]

This proves (5.5); the case \(z=1\) is immediate. Taking \(z\le1/2\) yields (5.6). No step used independence, a fixed schedule, or advance knowledge of the choices; the bound applies to adaptive selection.

### 5.1 Transfer from the derivative to actual nearby ALS trajectories

The direction \(H\) is a realizable tangent direction at (5.1). To see this, change bases from \(e_1,e_2\) to \(u,v\) in all three modes. At the diagonal rank-two tensor, every binary triple has at least two equal coordinates. Its eight coordinate tensors therefore occur among the factor tangent directions of the two components. The tensor Jacobian is surjective, and an anchored eight-dimensional local factor chart has invertible derivative.

Choose a factor perturbation \(h\) with \(Jh=H\). Then the curve \(\theta(t)=\theta_*+th\) has residual \(tH+O(t^2)\). For any fixed finite block sequence, its actual least-squares map is analytic near the root, and the derivative residual is the projection product in Theorem 5.2. There are only finitely many possible block sequences up to a fixed length \(M\). Their Taylor remainder bounds can therefore be made uniform by taking a sufficiently small common neighborhood, even when a policy chooses its sequence from observed iterates.

Consequently, for fixed \(c,M\), the actual residual reduction ratio along this curve is bounded below by the right side of (5.5), up to a term tending to zero with \(t\). If \(M\eta^2<1/3\), sufficiently small nonzero perturbations cannot be halved in that budget by any policy in this block class.

This is a local worst-case statement. The small initial neighborhood may depend on \(c\) and \(M\); no random-initializer basin probability is asserted.

## 6. What the lower bound does not exclude

The construction is at width two. TR-09 asks for an asymptotic width function and permits choices beyond the block class analyzed here. Extra components, structured initializers, gradient-based procedures, or other permitted optimization operations are not excluded by Theorem 5.2. In particular, an asymptotically subquadratic width function need not have value two at rank two.

Nor does this theorem establish failure with high probability in the original smoothed model. A worst-case nearby trajectory, a derivative with a slow direction, and a random-start lower bound are distinct claims. Passing from one to another would require a separate basin and probability argument.

The result shows precisely why the mixed-block cycle cannot be justified for arbitrary coherence simply by reusing its two-orthogonal-mode derivative cancellation.

## 7. Exact checks and executable material

`verify_exact.py` uses only Python's standard library and exact rational arithmetic. It checks the entire parameter Jacobian through one mixed cycle in six configurations, including external coordinates, strongly coherent first-mode columns, and a rank-deficient first-mode matrix with pairwise noncollinear columns. The check is the matrix identity (3.2), not a collection of sampled tangent directions.

It also checks all nine two-component mode selections for five rational points on the unit circle. These verify the exact projection formulas (5.4) and \(s^4\), and check full tensor tangent rank in the rank-two construction. Running the script writes `exact_checks.json`; that file, when present, is the execution record. These finite identities are not a proof-assistant verification of the quantified theorems.

`mixed_als.py` implements actual mixed-block least squares and the binary cycle. It includes a diagnostic driver for small local examples. A local start constructed using true factors is explicitly a diagnostic input, not an admissible input-independent initializer for the global target. Numerical residuals, when recorded, are observations rather than certified error enclosures.

Reproduction:

```sh
python verify_exact.py
python mixed_als.py
```

The exact-check program needs no third-party packages. The numerical driver needs NumPy. `packaging_manifest.json` records which checks and preceding archives were available when this package was assembled. No program modifies the GitHub repository or any external account.

## 8. Proof audit and disposition

The positive argument proves nonsingularity of every root design, accounts for changes in the design under factor perturbations, treats every tangent cell, removes scaling nonidentifiability only in analysis, and derives the nonlinear conclusion from a finite analytic cycle. It does not confuse a vanishing tensor derivative with factor identifiability.

The negative argument gives exact block projection norms, permits adaptive schedules, realizes its slow tensor direction by factor perturbations, and restricts its nonlinear transfer to fixed finite budgets. It does not turn a local derivative bound into an unsupported global or smoothed impossibility theorem.

The outstanding TR-09 obligations remain a qualifying subquadratic-width procedure for arbitrary base coherence, a uniform route from the permitted random initialization to an effective convergence regime, and the required nested smoothing and initialization probabilities with a polynomial total operation bound. The present note does not establish these obligations.

Accordingly, this work does not support a full-resolution status. The previous proposed `PARTIAL` classification remains contingent on review of the preceding in-target staged theorem; these new local results are not an independent substitute for that theorem or its review.

## Sources and provenance

[1] OpenProblemsInNLA, **TR-09: Subquadratic overparameterization for iterative decomposition of smoothed tensors**, canonical problem location supplied in the conversation: https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/tensor-computations/TR-09/README.md. The target is also reproduced and discussed in [2]. This note makes no assertion about the live repository's current status.

[2] **TR-09: Staged ALS for unbalanced smoothed tensors**, preceding 17-page research report in this conversation, `TR09_staged_ALS.pdf`, especially Sections 1, 2, 6, and 8. Associated archive: `TR09_sparta_bundle.zip`. This is prior working material, not an independently reviewed publication.

[3] OpenProblemsInNLA, **README** and **CONTRIBUTING**, repository locations: https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/README.md and https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/CONTRIBUTING.md. No repository edit is performed or claimed by this package.
