# Deterministic discarded-direction cancellation

Proposed by root before implementation. All matrices and norms are literal
finite real Euclidean matrices, with no stochastic or selector premise.

Let E,X be n by n, Y n by r, Q n by r, G n by s, and J n by n.
Suppose E=X+Y Q^T, Q^T Q=I, and J E G=0. If Q^T G has a right
inverse P (s by r), then

  J E = J (X-X G P Q^T).

For nonnegative zeta,B,L, suppose each row of X has Euclidean norm <=zeta,
each row of XG has norm <=B, every row of J has l1 norm <=L. Then

  every row of J E has norm <= L * (zeta+B*opNorm(P)).

The proof uses only the right inverse identity, row-vector norm inequalities,
Q's isometry, and the row l1 triangle inequality. It has no dependence on
Y's norm. Empty discarded rank and empty dimensions keep literal meanings.
A corollary takes P to the actual Spectral.pinv(Q^T G) when its row Gram
matrix is positive definite, using the previously proved right inverse.
The supplied row-operation bound can be 2^s from EliminationBlock.lean;
no independence between XG and Q^TG is asserted or needed here.

Preimplementation independent review pending.
