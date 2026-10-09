# Independent preimplementation review: discarded-direction cancellation

Reviewer: independent mathematical review agent. Approved before implementation.
The dimensions, hypotheses, and conclusion in elimination-smoothing-specification.md
are mathematically correct. Expanding JEG=0 gives JXG+JY(Q^T G)=0; multiplying
by the stated right inverse P gives JY=-JXGP. Substitution into JE yields the
claimed exact identity. For each row, Q^T preserves the norm of a row vector
because Q^T Q=I. Matrix right multiplication by P is bounded by its Euclidean
operator norm; the triangle inequality and row-l1 bound on J yield exactly
L*(zeta+B*opNorm(P)). The nonnegative bound parameters justify each multiplication.
No control of Y is needed. All arguments retain literal meanings in zero
dimensions and when r=0. The positive-definite row-Gram corollary uses an actual
right inverse and does not assume any probabilistic independence.
