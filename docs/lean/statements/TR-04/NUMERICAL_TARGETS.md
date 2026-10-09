# TR-04 exact mathematical, numerical and computational specification

Author: OpenAI Codex AI agent `/root/infra_audit`, 2026-09-28. Preimplementation specification: two independent approvals must precede code, including approval of the concrete SVD machine below. Permanent ID `TR-04`; canonical path `tensor-computations/TR-04/README.md`; campaign base `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`. The full canonical page is preserved byte-for-byte as `ORIGINAL.md`, SHA-256 `614dfc1189a99b0c2de54a04b948c01d35301d468e0b723c7fcb34b9918957cf`. `source-lock.json` binds its TeX, old formalization and complete manuscript. No original file, status, ID or credit changes.

## Complete mathematical approximation target

There exist one uniform finite-description arithmetic/SVD program, a natural polynomial exponent k and one natural coefficient C>=1, preceding every order d>=3, every mode size `n_i>=2`, every positive prescribed rank `r_j>=1` and every dense **real** tensor A. The program returns a tensor X whose unfolding across every prescribed cut has actual real matrix rank at most r_j. If the optimal squared Frobenius error E*>0, its error is **strictly** less than `(d-1)*E*`; if E*=0, X=A exactly. Running cost is polynomial in the dense input size and numerical rank parameters, under the fully specified idealized arithmetic/SVD convention below.

This is the affirmative algorithm-existence answer expressly requested by the original alternative “find an algorithm or establish a complexity obstruction.” It is not a proof of that answer. No smaller uniform factor c<d-1, uniform positive gap in the ratio, finite-precision guarantee, bit-complexity claim, random success probability, or rank enlargement is introduced.

Let `n : Fin d -> Nat`, `r : Fin (d-1) -> Nat`, and tensor indices be the actual finite dependent product `Index(n) = (i : Fin d) -> Fin(n_i)`. A tensor is a function `Index(n) -> Real`. Let `N=product_i n_i`. Its squared Frobenius distance is `sum_{a : Index(n)} (A(a)-Y(a))^2`, including all N entries.

For cut `j : Fin(d-1)`, split modes at `j.val+1`. Row indices are functions choosing one index in each mode i with `i.val<=j.val`; column indices choose one in each remaining mode. Joining those disjoint assignments gives one full index. Define `Unfold(Y,j)` as the actual real matrix with that row/column index pair and entry equal to Y on the joined index. Equivalently, mixed-radix numerical row and column indices with the same partition are acceptable after checking their bijections. The prescribed cuts are exactly `1,...,j+1 | j+2,...,d` in one-based notation, covering every j from zero to d-2, not just the first or last unfolding.

`Feasible(Y)` means `forall j, Matrix.rank (Unfold(Y,j)) <= r_j`, using the actual real linear-algebra rank. No arbitrary `unfoldingRank` field is allowed. Overprescribed ranks above possible matrix rank are included; there is no feasibility or consistency restriction on the positive r_j. Zero tensors, rank deficiency and all exact singular-value ties remain in the input domain.

Define `E*(A,r) = sInf { e : Real | exists Y, Feasible(Y) and e=FrobeniusSq(A,Y) }`. This is the original attained minimum: zero is feasible, the set is nonempty and bounded below by zero, each rank constraint is a closed determinantal condition, and minimizing sequences can be confined to a bounded ball in this finite-dimensional space. This correspondence is part of independent mathematical review; no assumed optimizer or E* oracle enters the machine. In particular, E*=0 implies actual exact feasibility of A, and the zero-error branch requires tensor equality, not a tolerance or an impossible strict inequality at zero.

## Uniform finite arithmetic/SVD machine

The model is a concrete scalar indexed exact-real RAM, adapting the already implemented `NLA.Computation.ExactRealMachine` ordinary operations but using **no random instructions**. Its program has finitely many valid labels with initial label zero, finitely many real scratch registers and natural address/counter registers with register zero present, and a finite real scalar-constant table. Program data are fixed before every format, rank vector and tensor. No dimension-dependent advice or arbitrary evaluator/output/cost function may be quantified.

Each ordinary instruction is one of the existing concrete scalar arithmetic, square-root, real comparison, fixed-natural-literal, natural copy/increment/decrement/add/multiply/comparison, natural-to-real cast, scalar indexed real-store read/write, jump, or successful-halt constructors, with finite operand/register/continuation indices. All cost one. Real division by zero and negative square-root arguments cause a distinct failed state. There is no arbitrary real-to-natural conversion, floor, digit extraction, tensor optimizer, rank oracle or free matrix multiplication. Natural integer indexing is unit-cost in this arithmetic model; this is not the binary Turing model used for AV/IV targets.

Add one explicit rectangular full-SVD instruction. Its operand fields name natural registers holding dimensions m,l and input/output base addresses, plus a next label. It reads the m-by-l real matrix B at row-major addresses in the **old** store. A legal response consists of concrete real matrices U of size m-by-m and V of size l-by-l and a real vector sigma of length `min(m,l)` satisfying:

```
sum_a U_ai*U_aj = (if i=j then 1 else 0),
sum_a V_ai*V_aj = (if i=j then 1 else 0),
forall k, 0 <= sigma_k; sigma is nonincreasing,
forall i j, B_ij = sum_{k<min(m,l)} U_ik*sigma_k*V_jk.
```

The full orthogonal bases and exact reconstruction specify actual singular-value data, including zeros; no approximate SVD or arbitrary subspace law is assumed. Dimension-zero cases have their usual empty-matrix meaning. The instruction writes all entries of U, then sigma, then V to three explicitly addressed consecutive row-major blocks. The three output blocks must be disjoint; otherwise the step fails. The input may overlap an output block, since the whole old input is read before any output update. Every other cell, counter and scratch register is unchanged. An ordinary program must charge any additional reshaping, copying, matrix product or error computation through scalar operations.

The SVD instruction costs exactly `(m+l+1)^3` units. This positive polynomial charge dominates reading/materializing all its input and output entries and is a fixed cubic dense-SVD convention. Using another usual positive polynomial dense-SVD charge yields the same polynomial-existence question after polynomial rescaling, but no uncharged unbounded bulk-output operation is allowed. Cost is the sum of these explicit charges and the unit ordinary charges along the actual executed trace; it is not a caller-supplied estimate. Terminal absorbing transitions have zero cost and are not new executed instructions.

Exact SVD has sign and tied/zero-space basis choices. The transition relation must permit **every** tuple satisfying the displayed equations. The finite program must satisfy the runtime and output guarantee for **every legal response trajectory**. This prevents a selected SVD choice function from encoding input-specific answers in a tie basis. A fixed admissible deterministic SVD convention makes this finite program a deterministic algorithm, as requested by the source; different valid conventions need not return the same tensor, but every allowed output obeys the same target. This robust SVD-primitive convention is explicit, rather than a claimed canonical choice of singular vectors. The archived finite-window algorithm's proof permits any starting orthonormal basis of a tied singular space, so its advertised resolution is compatible with the convention. There are no probabilistic draw streams.

## Concrete input, output and execution quantifiers

Initially natural register zero contains d; all other natural registers and all real scratch registers are zero, the initial label is zero and status is running. The real indexed store contains:

```
addresses 0,...,d-1:              the exact real casts of n_0,...,n_(d-1),
addresses d,...,2*d-2:            the exact real casts of r_0,...,r_(d-2),
addresses 2*d-1,...,2*d-2+N:       every entry of A in mixed-radix row-major order,
all remaining addresses:         zero.
```

For a full index a, its dense offset is `sum_i a_i * product_{s>i} n_s`. This is a bijection from Index(n) to `{0,...,N-1}`; the final mode varies fastest. Initialization can use quotient/remainder to describe that fixed input placement, but these are not new executable real-to-integer instructions. The input supplies only d, n, r and A, with no unfolding ranks, singular subspaces, E* or optimal tensor. Since every n_i>=2 and d>=3, the dimension/shape overhead is polynomial in N. A program can recover natural dimension/rank counters from their real input values through charged counter/cast/comparison loops; polynomial dependence on numerical rank parameters permits this without adding a floor primitive.

Successful halt returns the N consecutive real entries beginning at the natural address held in a designated finite register, interpreted by the same fixed mixed-radix bijection as a tensor X of the original format. A pointer return does not compute entries for free. Charging an extra N output serialization operations is absorbed by the same polynomial scale. Failed states have no output; successful and failed terminal states are absorbing. There is no storage bound in the original target, so none is added.

Define the structural legal transition relation by case analysis on those finite constructors and the explicit SVD equations, recording each step's fixed natural cost. A legal infinite trajectory starts in the stated initial state and follows that relation at every step, continuing terminal states by zero-cost identity. Such trajectories exist: ordinary instructions either step or fail, and every finite real matrix admits a full SVD. To exclude accidental vacuity from an implementation error, the target may explicitly conjoin existence of a legal trajectory with its universal behavior requirement; this is always a wellposedness fact of the stated machine semantics, not an input promise.

Set the natural size parameter `Size(d,n,r)=N+d+sum_j r_j+1`. The complete algorithmic quantifier order is

```
exists finite Program P, exists C k : Nat, 1<=C and
  forall d,n,r with d>=3, every n_i>=2, every r_j>=1,
  forall real tensor A,
    a legal trajectory from the concrete input exists, and
    forall legal trajectories tau,
      exists t : Nat and tensor X,
        tau(t) is a successful halt returning exactly X,
        sum_{s<t} stepCost(tau(s),tau(s+1)) <= C*Size(d,n,r)^k,
        Feasible(X),
        (0<E* -> FrobeniusSq(A,X) < ((d:Real)-1)*E*),
        (E*=0 -> X=A).
```

All running-step charges are positive, so this is worst-case polynomial termination and correctness for all legal SVD choices, not existence of a favorable short branch. The single C,k and program precede every input and every SVD response, with no hidden format/rank-specific constants. A polynomial in the sum of dense size and rank parameters is equivalent to an ordinary fixed multivariate polynomial bound in those numerical parameters. It does not claim a polynomial bound in the bit lengths of huge rank numbers or a bit bound for arbitrary real input.

## Source algorithm and quantitative correspondence retained

The retained Colbrook manuscript's algorithm is proof context, not a free primitive or an assumed witness to Target. If A=0 it returns zero. Otherwise its first unfolding has tail energy `e^2=sum_{i>r_1}sigma_i^2`, with singular values beyond the matrix dimensions interpreted as zero. If its rank is at most r_1 it uses its column space. Otherwise tau is the positive boundary singular value, H is the space for values strictly above tau, E the tau-space, h=dim H, t=dim E and s=r_1-h with `1<=s<=t`. For s=t one first space suffices. For s<t, every orthonormal basis of E yields the t cyclic windows of length s, and each basis vector occurs in exactly s windows. Their projectors average to `(s/t)*P_E`.

Each tested first space is completed by TT-SVD at unchanged remaining ranks. There are at most n_1 spaces and at most n_1 completions, but this count alone is **not** a runtime bound. Every product, exact singular-value equality test, dense reshape, error evaluation and minimum-candidate selection has arithmetic/SVD cost. Final equal-error ties can be resolved by the candidate's fixed enumeration index. No oracle for E* or an optimal Y appears in the algorithm.

For every feasible comparison Y, the completion estimate is `||A-X_U||_F^2 <= ||(I-P)A||_F^2 + (d-2)||P(A-Y)||_F^2`. The first-cut tail satisfies e^2<=E*. In the equality case e^2=E*>0, P_H annihilates the residual; if s<t the average projection energy is at most `(s/t)E*<E*`, giving a candidate factor `1+(d-2)*s/t<d-1`. The s=t case and zero optimum are separate and retained. These are source proof lemmas, not replacement target assumptions.

The fixed format 3-by-3-by-2 with ranks (2,1) and `A=alpha*e1⊗e1⊗f1 + beta*e2⊗e2⊗f1 + gamma*e3⊗e3⊗f2`, `alpha>gamma>=beta>0`, has E*=gamma^2. For gamma>beta the algorithm ratio is `1+(beta/gamma)^2`; alpha=2, beta=1, gamma decreasing to one makes it approach 2=d-1. Therefore the strict pointwise target must not be strengthened to a uniform factor c<d-1. Exact tied singular values must not be replaced by floating tolerances.

## Older formalization omissions and verification boundary

The retained old `lean/Challenge.lean` takes `unfoldingRank` as an arbitrary function field of ProblemData. It then quantifies a separate unrestricted function `algorithm : Tensor p -> Tensor p × Nat` for each format p, constraining its supplied natural result only by `<=n_1`. That natural need not count any operations or SVD completions; the evaluator has no finite syntax or transition semantics. Consequently the old declaration neither fixes actual TT rank nor asserts one uniform polynomial-time algorithm. Its two proved support lemmas are natural-number inequalities about a candidate count; they do not resolve these statement gaps or prove the approximation guarantee. Preserve all existing files and credit while replacing these holes in the new independent statement package.

Matthew J. Colbrook, University of Cambridge, retains resolution authorship; Oseledets and the workshop question retain their source credit. The inspected complete manuscript raw-byte SHA-256 is `e7770aa08ee91fbda82e0bfe3e087f1a9c8ee2a076218144bf0040e4d282bf73`. AI-assistance and informal independent-review disclosures remain unchanged.

Implementation must supply actual finite instruction syntax, SVD reconstruction/orthogonality predicates, charged transition and trace semantics, input/output layout, unfolding matrices, exact rank and Frobenius quantities before calling Target complete. No target axiom, assumed evaluator, assumed cost or unimplemented semantic parameter is allowed. The solver and its correctness proof need not be constructed merely to define this closed proposition. Review any implementation change to these model choices before claiming correspondence.

Use the shared pinned Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. Final independent review must include the entire shared arithmetic/SVD import closure, exact finite rank convention, every trace/cost quantifier and all tied/zero singular-value cases. Kernel statement/trust and frozen Comparator identity checks do not prove Target. No numerical tensor sampling or interval computation is required to state it.
