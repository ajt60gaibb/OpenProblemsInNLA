# RA-04: complete clustered-gap Krylov statement

Specification author: OpenAI Codex AI agent `/root`, 2026-09-28. This specification precedes implementation and requires two independent approvals. Full canonical README is preserved byte for byte as ORIGINAL.md, including original target, resolution, credit and historical notes. Source-lock.json binds the canonical page, problem.tex and archived full report. Permanent ID, path, status and old files remain unchanged.

## Original target and exact quantifiers

There exists one real constant C>0, independent of every input, such that for every natural n,d,b,k, every real n-by-d matrix A, 1<=b<=k, t=ceil(k/b), m=b*t<=rank(A), and real 0<epsilon,delta<1/2, the exact Gaussian Krylov output at

q = ceil(C * ((t:Real)/sqrt(epsilon)*log(2/Delta) + (1/sqrt(epsilon))*log(n/(delta*epsilon))))

has the three simultaneous guarantees below with probability at least 1-delta. All ceilings in t,q are nonnegative integer ceilings; t may equivalently be (k+b-1)/b in natural arithmetic. All logarithms are natural. The matrix-rank requirement implies n,d>=1 and k<=min(n,d). No extra rank, spectral-width, tail positivity, conditioning or consecutive-gap premise may be added.

For zero-based indices define sigma(A,j) as the actual j-th ordered singular value of the Euclidean linear map of A, padded by zeros beyond min(n,d), and lambda(A,j)=sigma(A,j)^2. Set

Delta = min_{0<=i<m-b} (lambda(A,i)-lambda(A,i+b))/lambda(A,i)

with the empty minimum exactly 1, and require Delta>0. Since m<=rank(A), every denominator is positive. The implementation may form the nonempty finite minimum using sInf of its explicitly finite set, with a separate empty branch; no arbitrary infimum convention may replace the specified 1.

## Concrete Gaussian law, subspace and output

The draw G is an actual n-by-b real matrix whose n*b entries are independent N(0,1), using the finite product of gaussianReal 0 1 over Fin n times Fin b. This is the sole randomness. Let M=A*A transpose and K be the real span of the vectors M^j times column a of G for j in Fin q and a in Fin b. Powers are exactly j=0,...,q-1; there is no perturbed input, resampling, alternative start or shifted degree.

For every natural r and every real n-by-r matrix Z whose columns are orthonormal and whose column span equals K, let B=Z transpose*A. Use the full ordered right spectral representation of B: choose a real d-by-d orthogonal V and nonnegative antitone lambdaB:Fin d->Real satisfying

B transpose*B = V*diagonal(lambdaB)*V transpose.

Define the SVD truncation concretely by

Truncate(B,V,k)_{a,j} = sum_{ell:Fin d, ell<k} (sum_h B_{a,h}*V_{h,ell}) * V_{j,ell}.

Then Ahat=Z*Truncate(B,V,k). This is B times the projector onto its selected top k right singular vectors, exactly a truncated SVD, including repeated and zero singular values. It avoids introducing a selected-SVD oracle and requires no arbitrary decomposition function. Every valid Z and V is covered. The orthogonal right spectral representation exists for every B, even r=0; the column-space basis exists for every finite-dimensional K. These elementary correspondence facts are not assumptions passed to the target.

The success event must quantify all such basis/decomposition choices for a single G. Within each output, it includes every full ordered right spectral decomposition of Ahat, with orthogonal W and nonnegative antitone lambdaHat satisfying Ahat transpose*Ahat=W*diagonal(lambdaHat)*W transpose. Thus the right vectors are columns W_i. This is the arbitrary-basis/arbitrary-tie convention of the source algorithm; a favorable selected singular vector is not substituted. Zero-eigenvalue directions are retained when the output has fewer than k nonzero singular values.

## Three guarantees on one event

Define the actual induced real Euclidean operator norm using the continuous linear map associated to Matrix.toEuclideanLin, not an entrywise function norm. FrobeniusNorm(X)=sqrt(sum_ij X_ij^2). For this one Ahat, require both

SpectralNorm(A-Ahat) <= (1+epsilon)*sigma(A,k),

FrobeniusNorm(A-Ahat) <= (1+epsilon)*sqrt(sum_{i:Fin(min(n,d)), k<=i} sigma(A,i)^2).

These are exactly the two best rank-k error benchmarks ||A-[A]_k||_2 and ||A-[A]_k||_F by the SVD tail formula, independent of ties. The source ranks are one-based; sigma(A,k) in zero-based indexing is the source sigma_{k+1}. There is no extra multiplicative square or conversion to squared error.

For every ordered full right decomposition W of Ahat and each i:Fin k, let v_i be its corresponding column. Also require

abs(sum_j ((A*v_i)_j)^2 - lambda(A,i)) <= epsilon*lambda(A,k).

The vector energy is the square of the actual Euclidean norm of A*v_i. All three bounds hold on the same event, whose measure under the concrete Gaussian product must be >=ENNReal.ofReal(1-delta). The original question is a per-input probability statement, not a simultaneous event across all A, epsilon or delta. C alone is chosen globally.

The event is expressible using finite real algebraic spectral, subspace, norm and output constraints for each fixed dimension, with finite rank/basis dimensions; its universal decomposition quantifiers are real-algebraic. No unmeasurable arbitrary choice is required. A future proof may establish that correspondence and measurability; no theorem or axiom asserting them is needed merely to define the concrete proposition.

## Boundary cases and scope

Retain b=k and t=1 (Delta=1), nondivisible k/b and padding m, n or d equal to one where permitted, exact zero optimal error/rank(A)=k, all repeated singular values allowed by the b-step gap, Gaussian rank failures, every allowed q and all rectangular sizes. The normal Gaussian product is defined even on exceptional draws; they are assessed by the same actual algorithm predicate rather than discarded as an input promise. The factor 2 inside log(2/Delta) must remain.

The source report Section 1 exactly reproduces this target; Section 7 treats zero tail separately and uses the same original Krylov output. The resolution's unknown convergence constant C0 and illustrative C=80*C0+4 are not fixed numerical inputs to this existential-C statement. No conditioning bound for the raw Krylov matrix, finite-precision extension, extra t*log(m) factor or separate conjecture from the source paper is included. No algorithm running-time target beyond the prescribed exact Krylov iteration count appears in the original.

## Lean and review obligations

Implement only after two independent exact-source approvals. Use concrete local helper definitions and pinned Mathlib APIs; a closed safe Target:Prop with LeanCert kernel trust, #assert_statement, #assert_trust kernel and a fresh frozen boundary. No target theorem, assumed probability/cost function or answer axiom is permitted. Review every zero-based index, finite minimum, natural ceiling, singular-value padding, subspace equality, rectangular multiplication, universal tie choice, exact norm, and shared probability event. Algebraic definitions suffice; no numerical experiments, huge tensor expansions or artificial interval certificates are needed. Frozen-boundary equality and kernel trust certify the statement's implementation, not the truth of this solved problem.
