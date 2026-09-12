# IV-01: a directed fixed-entry criterion

**Repository-target classification: NEW PARTIAL RESULT.** No proof or counterexample for unrestricted IV-01 is claimed. The theorem below has a complete proof candidate under a new explicit sufficient condition. Its historical novelty has not been established. The existing same-parity theorem is an explicit external input, not a result claimed as new here.

## 1. Exact target and notation

Let n>=5, L,U be real n by n matrices with L<=U entrywise, and epsilon be in {-1,1}^n. Define A=A^- by selecting L at positions with i+j even and U at positions with i+j odd; define B=A^+ by the opposite choices. Assume det A and det B are nonzero and every order-k minor d of either endpoint satisfies epsilon_k d>=0, for every 1<=k<=n. The question is whether every real M in [L,U] has these same properties, including nonsingularity. Zero minors are allowed and essential.

Source: [canonical IV-01 README](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/intervals-and-absolute-value-equations/IV-01/README.md), blob `4317a0f6303eebaf3894a31b992411540bb47533`, checked 2026-09-12.

Write chi_ij=(-1)^(i+j), J=diag(1,-1,1,...), and A<=*B when JAJ<=JBJ entrywise. Thus the original box is precisely the checker interval between A and B. Indices in this text start at 1; JSON and Python indices start at 0, which leaves i+j parity unchanged.

## 2. Main partial theorem

Let

    F0 = {(i,j): A_ij=B_ij=0},
    F1 = {(i,j): A_ij=B_ij != 0}.

Build a directed bipartite graph on row vertices R_1,...,R_n and column vertices C_1,...,C_n. For each (i,j) in F1 put

    C_j -> R_i   if epsilon_1 chi_ij = +1,
    R_i -> C_j   if epsilon_1 chi_ij = -1.

**Theorem G.** The conclusion of IV-01 holds if this directed graph is acyclic and the positions in F0, if any, all have the same i+j parity.

**Forest corollary.** In particular, the conclusion holds when all fixed entries are nonzero and their underlying bipartite incidence graph is a forest. Such fixed entries may have both checkerboard parities. The forest condition alone is NOT asserted to handle fixed zero entries of both parities.

The criterion is only sufficient. Directed cycles do not establish a counterexample. A singleton interval A=B can have many such cycles and is trivially valid.

## 3. External theorem used, checked against its full statement

Adm and Garloff, *Certification of the Sign Regularity of Matrix Intervals*, Acta Scientiarum Mathematicarum (2026), DOI [10.1007/s44146-026-00223-y](https://doi.org/10.1007/s44146-026-00223-y), Theorem 3.3, states the required two-checker-vertex implication for nonsingular SR endpoints of a common signature when all fixed positions of the interval have one parity (also when there are no fixed positions).

That theorem permits arbitrary signatures and zero minors, and applies to real square matrices. These are exactly the features used below. Theorem 3.2 in the same source concerns strictly SR endpoints only; it is not silently substituted for Theorem 3.3.

## 4. Proof of Theorem G

### 4.1 Directed acyclicity gives scaling potentials

Choose integers h(V) strictly increasing along each directed edge, for example the positions in a topological order. Put r_i=h(R_i) and c_j=-h(C_j). Then

    epsilon_1 chi_ij (r_i+c_j) > 0     for every (i,j) in F1.

Conversely, potentials with these strict inequalities cannot exist around a directed cycle, since their strict increases would sum to a contradiction. Thus the graph condition exactly characterizes feasibility of this particular strict diagonal-scaling perturbation.

For t>0 define positive diagonal matrices

    D_r(t)=diag((1+t)^r_i),    D_c(t)=diag((1+t)^c_j),
    B(t)=D_r(t) B D_c(t).

Negative integer exponents are allowed. Every multiplier is positive. A minor of B(t) is the corresponding minor of B times a positive product of row and column multipliers. Hence B(t) remains nonsingular SR with precisely the signature epsilon, and B(t)->B as t decreases to zero.

### 4.2 Opening the nonzero fixed entries

For (i,j) in F1, put a=A_ij=B_ij. Since the first-order sign-regularity assumption gives sign(a)=epsilon_1,

    chi_ij(B(t)_ij-A_ij)
      = chi_ij a [(1+t)^(r_i+c_j)-1] > 0.

The strict inequality follows from the potential inequality and the fact that, for t>0, the sign of (1+t)^s-1 is the sign of the nonzero integer s.

For (i,j) in F0, B(t)_ij=A_ij=0 exactly. At every other position the original checker gap chi_ij(B_ij-A_ij) is strictly positive. By continuity it remains strictly positive for all sufficiently small t>0. There are finitely many positions, so one common positive upper bound on t works for all of them.

Consequently A<=*B(t), and for all such t the fixed positions of the new interval are exactly F0. By hypothesis they have one parity or are absent. The external Theorem 3.3 therefore proves that every matrix in the new interval is nonsingular SR(epsilon).

### 4.3 Passing to the original interval

Fix any M in the original checker interval. At a nonfixed position set

    theta_ij=(M_ij-A_ij)/(B_ij-A_ij),

which lies in [0,1], whether B_ij-A_ij is positive or negative. At a fixed position set theta_ij=0. Define entrywise

    M(t)_ij=(1-theta_ij) A_ij + theta_ij B(t)_ij.

Then M(t) lies in the new checker interval and tends to M. All its signed minors are nonnegative. Since determinants of submatrices are continuous polynomials in the entries, every signed minor of M is nonnegative too.

Nonsingularity cannot be inferred merely by taking this limit. It follows instead from the original endpoint hypotheses by Lemma N below. This separate step is necessary: a limit of nonsingular matrices can be singular. Thus M is nonsingular SR(epsilon), proving Theorem G and its forest corollary.

## 5. Nonsingularity and cofactor control for every original interval

This is a useful general reduction, not a new resolution of the middle-minor issue.

**Inverse-positive box lemma.** Suppose P<=Q and both P^-1 and Q^-1 are entrywise nonnegative. Then every C in [P,Q] is nonsingular with C^-1>=0.

Proof. Set v=P^-1 1 and w=Q^-1 1. Both vectors are strictly positive, since a nonsingular nonnegative matrix has no zero row. Let T=Q^-1(Q-P)>=0. Direct multiplication gives Tv=v-w. Hence 0<=Tv<v. In the weighted maximum norm with weights v,

    ||T||_v = max_i (Tv)_i/v_i < 1.

For C in [P,Q], E=Q-C obeys 0<=Q^-1 E<=T. Therefore the Neumann series for I-Q^-1 E converges to a nonnegative inverse. As C=Q(I-Q^-1 E),

    C^-1=(I-Q^-1 E)^-1 Q^-1>=0.

Moreover Q^-1<=C^-1<=P^-1, by the identities

    P^-1-C^-1=P^-1(C-P)C^-1,
    C^-1-Q^-1=C^-1(Q-C)Q^-1.

This proves the lemma without an appeal to a Perron eigenvector theorem.

**Lemma N.** Under the original IV-01 endpoint hypotheses, every interval matrix is nonsingular; its order-1, order-(n-1), and order-n minors have the required signs.

Proof. Put delta=epsilon_(n-1)epsilon_n. The adjugate formula implies

    delta J A^-1 J >= 0,    delta J B^-1 J >= 0.

Indeed an inverse entry is a cofactor divided by the determinant, and the two J factors cancel its cofactor parity. Set K_A=JAJ and K_B=JBJ, so K_A<=K_B. If delta=+1, apply the inverse-positive box lemma to P=K_A,Q=K_B. If delta=-1, apply it to P=-K_B,Q=-K_A. In either case every original M is nonsingular and satisfies delta J M^-1 J>=0.

The box is connected and its determinant never vanishes, so det M has the endpoint sign epsilon_n everywhere. The adjugate identity now gives the sign epsilon_(n-1) for every cofactor minor, since epsilon_n delta=epsilon_(n-1). Entries have sign epsilon_1 or are zero because each scalar interval is bounded by entries with that same sign. This proves Lemma N.

Thus a counterexample, if one exists, must have a wrong-sign minor of order 2,...,n-2. Nonsingularity alone is not the remaining gap.

## 6. A nontrivial five-dimensional example covered by the theorem

The exact data are in `mixed_parity_example.json`; all 251 minors of each endpoint are separately recorded in `A_minus_all_minors.json` and `A_plus_all_minors.json`.

Here is a compact formula. For i=1,...,5 put z_i=i/6 and

    lambda=(1, 1/10, 1/100, -1/1000, -1/10000),
    H_ij=sum_(k=0)^4 lambda_(k+1) (z_i z_j)^k.

Let A equal H except that

    A_11 = H_11 - 500618646037/19352067067828800.

Set B_ij=A_ij+10^-8 chi_ij except at (1,1) and (1,2), where B_ij=A_ij.

Exact rational minor calculations establish the common signature

    epsilon=(+1,+1,+1,-1,+1).

A has exactly one zero minor: rows (1,2,3), columns (1,2,3), of order three. Its other 250 minors have strictly correct signs. B has all 251 minors strictly correctly signed. Both determinants are nonzero, and all entries of both endpoints are positive. Thus the example genuinely involves a vanishing middle-order minor, not just numerical near-degeneracy.

The only fixed entries are (1,1) and (1,2), of opposite parities. Their graph is C_1 -> R_1 -> C_2, with the remaining vertices isolated. Theorem G certifies the entire real interval, not merely its sampled matrices. It has 23 independently variable entries.

The signature is outside the 16 periodic/final-sign-flip patterns displayed in the cited survey: for n=5 those patterns have product epsilon_1 epsilon_2 epsilon_3 epsilon_4=+1, whereas this example's product is -1. This comparison is not a claim of an exhaustive novelty search over all published subclasses.

The script `build_and_verify_example.py` reconstructs the example, verifies every endpoint minor exactly, verifies the graph potentials and a rational positive diagonal perturbation opening all fixed entries, and tests 24 additional interval matrices. Those 24 tests are not used as a proof of the universal interval conclusion. The finite endpoint certificates are independently checkable integer/rational calculations.

### 6.1 Limitation of the first example

Because B in the first example is strictly SR, there is a simpler sufficient
argument: perturb B a sufficiently small amount in the strictly positive
checker direction, staying strictly SR by openness. The enlarged interval has
no fixed entries, so the external Theorem 3.3 applies and contains the original
interval. The corresponding argument applies if A is strictly SR. Thus the
first example is an illustration of the graph proof, not evidence that both
endpoint degeneracies have been addressed. The next example removes this issue.

### 6.2 A stronger example: both endpoints have zero middle minors

`both_boundary_example.json` gives a second interval with

    epsilon=(+1,+1,-1,+1,-1).

Put z_i=i/6 and

    lambda=(1,1/10,-1/100,-1/1000,-1/10000),
    H_ij=sum_(k=0)^4 lambda_(k+1)(z_i z_j)^k.

Form A from H by adding

    -33147818447311/12378920898816000

to entry (1,1). Form B0 by adding 10^-8 chi_ij to A outside the two fixed
positions (1,1),(1,2). Finally form B from B0 by adding

    2031265661033157499/47046190927957024752000

to entry (1,3). The script `build_both_boundary_example.py` derives both
boundary shifts from exact minor constraints and verifies these data.

A has exactly one zero minor, on rows (1,2) and columns (1,2), of order two.
B has exactly one zero minor, on rows (1,2,3) and columns (3,4,5), of order
three. Each endpoint's other 250 minors have strictly correct signs. Both
matrices are nonsingular, all entries are positive, and the fixed graph is
again C_1 -> R_1 -> C_2. Neither endpoint is strictly SR. Theorem G certifies
all real matrices in this 23-parameter interval. The signature again has
product of its first four components -1.

All 251 minors of these endpoints are in `A_both_boundary_all_minors.json`
and `B_both_boundary_all_minors.json`. The independent Leibniz audit checks
all four endpoints of the two examples, 1004 minor values, plus 251 for the cyclic-graph example below.

## 7. Further unconditional order-two reduction

`order_two_reduction.md` proves that all order-two minor signs are also forced
throughout the original interval. Its argument uses only nonsingular endpoints
with their common entry and order-two signs: an uncrossing argument supplies
positive diagonals after normalization, staircase zeros propagate through
checker bounds, and positive rectangles permit telescoping adjacent-minor
inequalities. Combined with Lemma N, this confines a counterexample to orders
3,...,n-2. For n=5 only order three remains. No complementary-inverse extension
to order n-2 is asserted.

## 8. A stronger dimension-five theorem

`dimension_five_theorem.md` proves Theorem V: if there are no fixed zero
entries and every fully fixed adjacent 2 by 2 block is nonsingular, all
order-three minors throughout the interval have the required signs. For n=5
this proves the entire nonsingular SR conclusion. For larger n it controls
order three only, leaving possible higher middle orders.

The proof does not use the external same-parity theorem. In the relative
interior, the order-two theorem forces strict adjacent order-two signs unless
an entire adjacent block is fixed and singular. Telescoping gives strict
order-two signs on arbitrary index pairs. All adjacent order-three minors
are checker-monotone because their cofactor minors have the known order-two
sign. A projective secant-slope argument then propagates the order-three sign
from adjacent triples to all triples. Continuity and the independent
nonsingularity lemma handle boundary matrices.

This handles some directed fixed-entry cycles. The exact example in
`cyclic_graph_dimension_five_example.json` is obtained from the both-boundary
example by also fixing positions (4,1),(4,2),(5,1),(5,2) to their A values.
Both endpoints remain non-strict SR(++-+-), with zero middle minors. Its
fixed graph has a directed cycle, so Theorem G does not apply. Its only fully
fixed adjacent 2 by 2 block has determinant

    15666947141/6122200320000 > 0.

Theorem V applies. `verify_dimension_five.py` verifies the endpoints, the two
criteria, and 64 supplementary samples. Its additional upper-endpoint minor
certificate is independently checked, bringing the total to 1255 exact
Leibniz comparisons across five distinct endpoint matrices.

## 9. What remains

The original problem permits cases not covered by these sufficient conditions. In dimension five, a counterexample must have a fixed zero entry or a singular fully fixed adjacent 2 by 2 block; neither condition by itself is a counterexample. In larger dimensions higher middle-order minors remain beyond the order-three reduction. The graph theorem also leaves cyclic graphs and fixed zero entries of both parities outside its own scope. The additional cycle-normalization reduction in `cycle_reduction.md` isolates a more specific obstruction but does not eliminate it. No repository status change is justified by this pack.
