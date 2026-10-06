# A1 spectral concentration: universal-constant proof route

Proposed by /root for independent mathematical review before implementation.
The main IE-06 target and all-Schur tail remain exactly unchanged. For the
Gaussian-only application, replace the source spectral auxiliary estimate by
the following sufficient explicit version (not a claim of its literal constants).
For iid standard Gaussian G:m-by-n, deterministic M:n-by-p, 1<=k<=min(m,p),
and x>0, prove

P{sigma_k(GM)>16 ||M||F+(16 sqrt(m)+sqrt(2x/k))||M||op}<=exp(-x).

The universal factor16 is absorbed into C_beta in the selected-block extension
estimate; the essential sqrt(x/k), Frobenius and sqrt(m) scalings remain intact.
No extra dimension or log-dimension factor is permitted.

Proof route: use a finite 1/2-net of the Euclidean unit sphere in R^m with at
most5^m elements. For each fixed unit vector y, y^T G has exactly the iid
standard Gaussian law, so the already proved quadratic tail bounds ||y^T GM||².
The exact operator net inequality is ||GM||op<=2 max_y ||y^T GM||.
Taking x=m log5+2 gives probability at most exp(-2) for
||GM||op>B=2 sqrt(2||M||F²+4(m log5+2)||M||op²).

The function G->||GM||op is ||M||op-Lipschitz for the genuine Euclidean
Frobenius metric. Apply the already proved Gaussian concentration to its
negative: P{||GM||op<E||GM||op-2||M||op}<=exp(-2).
Since2exp(-2)<1, these two estimates imply E||GM||op<=B+2||M||op.
The scalar inequalities log5<=4,m>=1 give B+2||M||op<=16(||M||F+sqrt(m)||M||op).
Integrability of this actual operator norm follows from proved Gaussian
Lipschitz integrability; zero M is treated directly.

For f_k(A)=sqrt(sum_(i<k)sigma_(i+1)(A)^2), prove the genuine variational
representation as the supremum of ||QA||F over k-by-m contractions Q. This
makes f_k(GM) ||M||op-Lipschitz in G and f_k(A)<=sqrt(k)||A||op.
Together with sqrt(k)sigma_k(A)<=f_k(A), its expectation and concentration at
sqrt(2x)||M||op prove the stated tail. One may equivalently define the
functional through the contraction supremum and prove these three exact
properties directly, without asserting an unproved sum-of-singular-values
identity. Actual product-Gaussian/Euclidean-coordinate laws must be bridged.

No comparison theorem, norm bound, integrability, Gaussian law or Lipschitz
property is introduced as an undisclosed hypothesis of the final estimate.
The finite-net bound is a generic proved volume/packing argument, not an
explicit enumeration of exponentially many points.
