# Mathematical audit notes

## General prescription: dependencies

1. Tensor realization makes the objective nonnegative and gives `B=max(lambda)^n` and Lipschitz constant `2*n*B` on the unitary group in Frobenius distance.
2. Power-sum equations plus the square-free matrix spectral equation describe the semisimple complex similarity orbit for every multiplicity pattern, including zeros.
3. Differentiating the permanent gives the permanental adjoint. Hermitian orbit stationarity implies commutation, without assuming distinct eigenvalues.
4. The differential vanishes on every irreducible component of the critical locus. Characteristic zero therefore forces the objective to be constant on each component. Critical points may form positive-dimensional families; critical values are finite.
5. Elimination is performed after fixing the spectrum. Its univariate polynomial contains the actual maximum, but real roots are not presumed feasible on the Hermitian orbit.
6. The rectangular row/column-group character formula is derived as the squared norm of a central projector. Weights are nonnegative and sum to one. The partition-length cutoff handles moment degree greater than dimension.
7. A packing argument bounds Haar mass of a Frobenius ball around a maximizer. Combining it with the Lipschitz estimate yields an explicit finite moment order for which the moment root is less than half a candidate spacing below the maximum.
8. The exact maximum is then the first candidate not below that moment root. No real-feasibility solver, unknown optimizer, or unbounded limiting process is left in the prescription.

This is a generic algebraic answer. It does not itself provide the concise structural spectral formula often sought in extremal matrix problems. Historical novelty and acceptance as the intended resolution of MI-16 have not been established.

## One-exceptional family: dependencies

The user pack supplies the rank-one perturbation expansion and minimum-support averaging lemma. The new support activation calculation has a positive derivative for every support `3 <= k < n`; the sign proof uses an exact gamma-moment recurrence and separately checks `k=4`. Support one is strictly worse than support two. Positive perturbations use nonnegative elementary-symmetric coefficients; rank one at `beta=0` uses AM-GM.

The transition proof uses an exact differential identity and a strictly decreasing integrating-factor expression, not numerical root counts. Its endpoint sign treats odd and even order separately. The increasing-threshold proof embeds an order-n optimizer in order n+1 and activates a zero coordinate. The asymptotic expansion has an explicit uniformly integrable remainder and an exponentially small far tail.

The equality proof handles arbitrary maximizers, not only minimum-support ones. A hypothetical nonuniform maximizer can be merged without changing its value. The last merge into support two forces `x=2/3`, where support three is strictly better, a contradiction.

## Evidence versus proof

The exact scripts independently check permanent identities, group characters, Haar moments, recurrence identities, transition polynomials, finite grids, small eliminations, and root selection. Finite checks cannot replace proofs for all orders. The optional floating-point searches are not certificates and support no universal claim. Generic order-three elimination did not finish within its explicit process budget.
