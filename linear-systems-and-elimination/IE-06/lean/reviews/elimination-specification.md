# Elimination operator: reviewed deterministic contract

Author: coordinating agent `/root`. Independent preimplementation approval:
`/root/source_statement_author`, received before code was written.

For input A and a fixed path p, let S_k be the frozen exact Schur trajectory.
Define E_0=I. For k<n, write B=rowSwap(S_k,k,p_k) and
R=rowSwap(E_k,k,p_k), and set

E_(k+1)[i,j] = R[i,j] - (B[i,k]/B[k,k]) R[k,j] for i>k,
and zero for i≤k. For k≥n set the next operator to zero.

The precise claims are:

1. For every original column j with k≤j, (E_k A)[i,j]=S_k[i,j]
   for all rows i, including inactive rows. This holds even for a fixed invalid
   path; total division merely makes the algebraic map total.
2. E_k has zero rows at indices i<k. In particular E_n=0.
3. If the complete path is admissible, every row of E_k has sum of absolute
   entries at most 2^k. The nonzero pivot and active-row restrictions are retained.
4. For a fixed path, E_k depends only on original columns with index less than k.
   An auxiliary Schur-column dependence lemma includes these prior columns and
   the queried column. This does not assert the same for an arbitrary
   data-dependent path; the canonical pivot rule needs its separate dependence
   proof.

The reviewer checked the endpoint cases and induction: the multiplication
identity uses the old relation at columns k and j, the l1 estimate uses a
multiplier of absolute value at most one, and the final update has no surviving
rows. The claims are F4/F9 infrastructure for the full argument and do not
replace any probabilistic or selected-block theorem.
