# Actual GEPP pivot conditioning: exact staged contract

This is the F7 dependency, not a claim that its proof is complete. The conditioning information is exactly the first t selected original row labels and their first t entries, as in Section 5 of the retained manuscript. It is different from revealing all first t columns.

## Original labels and a finite partition

Fix natural n,t with t at most n. All statements include t=0 and t=n. Let gamma_n be the existing concrete gaussianMatrix n. The frozen firstPath chooses current row positions, so it must first be converted into original labels.

For any active path p, define a permutation L_p(k) from current positions to original labels by L_p(0)=identity and
$$
L_p(k+1)(i)=L_p(k)(\operatorname{swap}(k,p(k))(i)).
$$
For the actual path, the original pivot at step j is
$$
\pi_t(A)(j)=L_{\mathrm{firstPath}(A)}(j)(\mathrm{firstPath}(A)(j)),
\quad j<t.
$$
The implementation must prove that these labels are pairwise distinct, that they equal L_p(t)(j) for j<t, and that the resulting embedding from Fin t to Fin n is measurable and depends only on the first t columns. Actual firstPath is active even on degenerate inputs, so the finite events P_pi={A:pi_t(A)=pi}, indexed by embeddings pi:Fin t into Fin n, partition the entire matrix space. No arbitrary pivot selector is substituted.

For fixed pi, let R_pi be the subtype of original row labels outside its range. Define
$$
T_\pi(A)_{rj}=A_{\pi(r),j},\qquad
Z_\pi(A)_{ij}=A_{i,j}\quad(i\in R_\pi,\ j<t).
$$
These are fixed-coordinate projections. Retaining the original-label subtype avoids silently changing row order; increasing enumeration can be supplied later as a deterministic equivalence. The pair (T_pi,Z_pi) has the literal product Gaussian law on the t selected rows and the n-t remaining rows. All columns at least t integrate out with mass one. A fixed row-coordinate measurable equivalence, not a dimension-counting assertion, will prove this factorization.

## Prescribed pivot rows and the common constraint body

For T in real t-by-t matrices, perform the existing totalized elimination with the identity pivot path on T, and let U_T(j,c) be the stage-j pivot row, zero for c<j. Write u_j=U_T(j,j). Define the residual of an arbitrary original row x recursively by
$$
r_0(T,x)=x,\qquad
r_{j+1}(T,x)_c=r_j(T,x)_c-
 \frac{r_j(T,x)_j}{u_j}U_T(j,c),
$$
and its multiplier lambda_j(T,x)=r_j(T,x)_j/u_j. Every quotient uses Lean's ordinary totalized real division, including at zero. Define
$$
K(T)=\{x:\ \forall j<t,\ |\lambda_j(T,x)|\le1\},
\qquad
K^\circ_*(T)=\{x:\ \forall j<t,\ |\lambda_j(T,x)|<1\}.
$$
The second set is the strict slab intersection; the notation does not assert it equals the topological interior without proof.

Planned unconditional geometric statements:
- For every fixed T, each residual coordinate and multiplier is a real continuous linear functional of x; dependence on (T,x) is Borel measurable.
- K(T) is closed, convex and centrally symmetric. The strict slab intersection is open and contains zero. Thus the standard t-dimensional Gaussian mass q(T)=gamma_t(K(T)) is strictly positive and at most one, including singular T and t=0.
- For every T, gamma_t(K(T) minus the strict slab intersection)=0. Each boundary lies in an affine hyperplane lambda_j(T,x)=1 or -1; a zero functional has no such level set. This null-boundary statement does not presume T is invertible.
- If every u_j is nonzero, U_T is invertible, the multiplier row satisfies lambda(T,x) U_T=x, and K(T) is precisely the manuscript body defined by the infinity bound on x U_T^{-1}. This bridge retains the full original interpretation; no SVD is needed.

Define Good(T) to mean that all u_j are nonzero and, for each j<s<t,
$$
|\lambda_j(T,T_{s,:})|<1.
$$
Thus the prescribed selected rows themselves strictly respect their prescribed pivot order. This condition involves only T, not the unselected rows or any later columns.

## Deterministic fibers and exceptional inputs

For fixed pi and T with Good(T), reconstruct a first-t-column matrix from T and arbitrary remaining original rows Z, and fill later columns by zero. The required deterministic sandwich is
$$
\{Z:\forall i\in R_\pi,\ Z_i\in K^\circ_*(T)\}
\subseteq\{Z:\pi_t(\mathrm{assemble}(\pi,T,Z))=\pi\}
\subseteq\{Z:\forall i\in R_\pi,\ Z_i\in K(T)\}.
$$
The left inclusion gives a unique maximum at every step, hence is independent of tie policy. The right inclusion follows from actual maximality. This must be proved using the actual evolving current-to-original label permutation and actual padded Schur trajectory.

For almost every T under the product law of its t rows, the fixed fiber of P_pi is empty if Good(T) fails. The only nonempty excluded possibilities are zero pivots or equality of a chosen pivot with a later prescribed pivot row. Their nullity will be proved, not assumed: stage-j pivot data depend only on earlier prescribed rows; a new prescribed row has a Gaussian coordinate with nonzero coefficient in its current residual. Fubini gives nullity of zero pivots and of the relevant affine equalities. Existing polynomial-null results are an alternative if their exact nonzero-polynomial premises are discharged.

Combining this with the strict/closed slab null-boundary result makes the fiber equal, almost everywhere in Z, to the product restriction to K(T), for almost every T. Canonical tie decisions are retained exactly on the original event; they are discarded only on proved null sets. No positive-probability exceptional set is union-bounded over pivot orders.

## Exact fixed-order integral identity

Let Gamma_t be the product of t standard t-dimensional Gaussian row laws, and let Lambda_pi be the product of standard t-dimensional Gaussian row laws indexed by R_pi. For every fixed pi and every jointly measurable nonnegative ENNReal test function F(T,Z), prove
$$
\int_{P_\pi} F(T_\pi(A),Z_\pi(A))\,d\gamma_n(A)
=
\int 1_{\mathrm{Good}(T)}
 \left[\int_{\forall i,\ Z_i\in K(T)}F(T,Z)\,d\Lambda_\pi(Z)\right]d\Gamma_t(T).
$$
This is a tested integral identity for the actual pivot event, not an assumed regular conditional distribution. The zero-dimensional product laws have their usual singleton mass one.

The already defined normalized restriction nu_T=restrictedGaussian(K(T)) is a probability law because q(T)>0. Product restriction and normalization then give the equivalent right side
$$
\int 1_{\mathrm{Good}(T)}q(T)^{|R_\pi|}
 \left[\int F(T,Z)\,d\left(\prod_{i\in R_\pi}\nu_T\right)(Z)\right]d\Gamma_t(T).
$$
Joint measurability of the body and these integrals must be established from the measurable multiplier formulas. This identity is the precise product conditional row law given the selected original labels and pivot block. Constructing an abstract conditional-probability kernel is optional if the tested integral theorem suffices for subsequent estimates.

## Adaptive consequence without a factorial loss

For a family of jointly measurable bad events B_pi(T,Z), suppose their probability under the product of nu_T laws is at most epsilon for every Good(T), or for Gamma_t-almost every such T. Then prove
$$
\gamma_n\{A:\exists\pi,\ A\in P_\pi,\
 (T_\pi(A),Z_\pi(A))\in B_\pi\}\le\epsilon.
$$
The fixed-order contributions are integrated with their actual weights. Applying the fixed-order identity to F=1 and summing the disjoint partition gives total weight exactly one. The number of embeddings never multiplies epsilon.

For the manuscript application, measurable matrices determined by T may enter each B_pi. The already proved GaussianRestriction quadratic tail applies independently to each row under the product restriction; a union over remaining row labels costs at most n-t. No independence after additionally conditioning on future-stage success is asserted. No measurable singular-value decomposition is assumed in this conditioning theorem.

## Planned bounded implementation order

1. Original row-label permutation, measurable injective prefix, and fixed-order coordinate factorization.
2. Prescribed residual multipliers and common body's geometry, positive mass, and null boundary.
3. Actual deterministic fiber sandwich and proof of the exceptional-T null set.
4. Fixed-order integral identity, normalization, and adaptive transfer using partition mass one.

Each stage will be kernel checked. This entire contract is submitted for independent mathematical review before any GaussianPivotConditioning implementation.
