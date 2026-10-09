# RA-05: complete strong-coreset size classification and original proposal

Author: OpenAI Codex AI agent `/root`, 2026-09-28. Preimplementation specification requiring two independent approvals. ORIGINAL.md retains the full canonical README byte for byte, including all historical partial results and credit. Source-lock.json binds the canonical source and both complete classification parts. Permanent ID, canonical path, status and original mathematical question remain unchanged.

## Full original scope and named propositions

The original asks to determine the optimal worst-case support size jointly in k and epsilon, up to logarithmic factors, for every fixed real p>2, and separately asks whether its displayed additive proposal holds. Merely defining a worst-case quantity or asserting the existence of some bound would not answer the first question. The implemented library must state the exact resolved classification below and retain the literal original additive proposal as a separately named closed proposition. Its negative answer must also be separately named, rather than silently replacing that proposal by another inequality.

Use `OriginalAdditiveConjecture := forall p>2, AdditiveProposal(p)`, `Classification` for the full rate theorem for every p>2, and `NegativeAnswer := forall p>2, not AdditiveProposal(p)`. The complete answer boundary `Target := Classification and NegativeAnswer` addresses both original requests, while OriginalAdditiveConjecture explicitly retains the original (false) subsidiary conjecture. No proposition is proved merely by defining it. In particular do not conjoin Classification with the false OriginalAdditiveConjecture, and do not identify a negative answer with a proof that some coreset is impossible.

## Concrete strong original-row coreset

For every n,d:Nat, every real n-by-d matrix A, integer 1<=k<d, real p>2 and 0<epsilon<1/2, a weight vector w:Fin n->Real is nonnegative. Its support size is the finite cardinality of {i | w_i != 0}, not sum_i w_i and not a count with repeated copies. Arbitrary real weights, including zero and fractional weights, are allowed, but negative weights are forbidden.

Represent every fitted real linear subspace of dimension at most k by its actual orthogonal projection P, a real d-by-d matrix with P transpose=P, P*P=P and Matrix.rank(P)<=k. Every such P is precisely a Euclidean orthogonal projector; conversely each real subspace has a unique such projector. This concrete equivalent representation must be inspected during final review and is not supplied as an uninterpreted semantic predicate.

For a row i put

residual_i(P)_j = A_ij - sum_h A_ih * P_hj,
cost_i(P) = (sqrt(sum_j residual_i(P)_j^2))^p,
Cost(A,P) = sum_i cost_i(P).

The exponent p is genuine real exponentiation of the nonnegative Euclidean norm. The zero row/cost convention is exactly 0^p=0 for p>2. StrongCoreset(A,p,k,epsilon,w) means w>=0 and, for EVERY P with those projector/rank conditions,

(1-epsilon)*Cost(A,P) <= sum_i w_i*cost_i(P) <= (1+epsilon)*Cost(A,P).

Both sides are non-strict; the same w must work simultaneously for every subspace, including the zero subspace and all ranks below k. No restriction on the rank, conditioning, signs, row norms or ambient dimension of A appears. All-zero and empty-row matrices are permitted; they do not affect worst-case lower bounds. Weights select original rows only. A low-rank replacement matrix, signed combination, weak coreset for one optimizer or approximate projection changes the target.

## Actual optimal worst-case size

For each individual A,p,k,epsilon, define

MinimumSupport(A,p,k,epsilon) = sInf {s:Nat | exists w, StrongCoreset(A,p,k,epsilon,w) and supportSize(w)<=s}.

On the target domain this nonempty natural set contains n by taking all weights equal to one. Its infimum is therefore its actual attained least support budget. It is not a totalized minimum of an empty set. Using the finite set of attainable support cardinalities is an equivalent implementation.

Define S(p,k,epsilon) in ENNReal as the supremum of

{ (MinimumSupport(A,p,k,epsilon):ENNReal) | n,d:Nat, k<d, A:Matrix(Fin n)(Fin d)Real }.

This is a supremum over all finite row counts, ambient dimensions and matrices, with no common upper bound on their sizes or input rank. The set is nonempty (e.g. n=0,d=k+1); the extended-real supremum handles potential unboundedness faithfully. A later finite upper bound proves finiteness; do not use the real sSup convention that assigns a default to an unbounded set. Coercions of support budgets into ENNReal are exact nonnegative-natural embeddings.

## Full resolved rate with explicit logarithmic losses

For p>2 let EvenPower(p) mean `exists s:Nat, 2<=s and p=2*(s:Real)`. This captures every allowed positive even integer and no non-even real. Set

L(k,epsilon)=Real.log(2*(k:Real)/epsilon),
R(p,k,epsilon)=
  min { (k:Real)^(p/2)/epsilon^2,
        (k:Real)^((p+1)/2)/epsilon + (k:Real)^(p/2-1)/epsilon^2 }
  if EvenPower(p),
  (k:Real)^(p/2)/epsilon^2 otherwise,
b(p)=0 if EvenPower(p), and 5*p/2+3 otherwise.

All exponents/subtractions are real, the min has exactly the two displayed even branches, and L>1 on the target domain. `Classification` states

forall real p>2, exists real c C, 0<c and c<=C and
  forall integer k>=1, forall real 0<epsilon<1/2,
    ENNReal.ofReal(c*R(p,k,epsilon)/L(k,epsilon)^b(p)) <= S(p,k,epsilon),
    S(p,k,epsilon) <= ENNReal.ofReal(C*R(p,k,epsilon)*L(k,epsilon)^(p+5)).

The same c,C depend only on p; they precede k and epsilon and all data implicit in S. Constants are finite real numbers. These exact exponents are the retained complete Part I Theorem 1.1/Part II Theorem 1.1 answer, stronger than merely unspecified polylogarithmic losses but within the original requested classification. They must be labelled as the resolved answer, not as constants or formulas conjectured in the original page. A p-dependent real logarithmic power is allowed by the source, with no lost polynomial factor hidden in that notation. For even p the lower bound has no logarithmic loss.

This gives both a worst-case obstruction and a uniform upper support bound. A witness-based equivalent formulation may be used only after reviewing its relation to this natural minimum/extended supremum; do not inadvertently require attainment of a general real supremum over all matrices. Directly using the ENNReal supremum avoids that additional issue.

## The literal subsidiary proposal and its negative answer

For each fixed real p define AdditiveProposal(p) to mean

exists real Cp cp, 0<Cp and 0<cp and
  forall n,d,k:Nat, 1<=k and k<d,
  forall real A:Matrix(Fin n)(Fin d)Real,
  forall real epsilon, 0<epsilon<1/2,
    exists w, StrongCoreset(A,p,k,epsilon,w) and
      (supportSize(w):Real) <=
        Cp*((k:Real)^(p/2)/epsilon+(k:Real)/epsilon^2)*L(k,epsilon)^cp.

Cp,cp are chosen before every input and depend only on p. The real cp>0 is the literal original logarithmic exponent. The negative answer is universal over p>2 and negates this whole proposition, allowing counterexample dimensions, matrices and accuracies to depend on attempted constants. It is not merely one p=4 example, failure at a sampled epsilon, or failure of a particular construction. The literal positive proposal remains separately stated as OriginalAdditiveConjecture.

## Original endpoints, provenance and computation

Include k=1 and every positive rank, every real exponent p>2 (including arbitrarily near an even integer), all epsilon in (0,1/2), any n and any d>k. Do not specialize to hyperplanes d=k+1, bounded input rank, p=4, even exponents, nonnegative data or a high-accuracy regime. Those appear in supporting constructions, not the full question. No efficient construction or running-time target is part of the original: this is an existence/support-size problem.

Part I Section 1 defines S using this precise original-row model and supplies the non-even lower logarithmic loss and common upper loss. Part II Section 1 gives all-accuracy even classification. Historical notices in Part II concern its earlier scope and do not supersede the later full statement. Sidney Holden retains resolution credit; Lin–Mirrokni–Woodruff retain the imported general upper-bound credit and Li–Wang–Woodruff the antecedent Fourier mechanism. Original README and complete source snapshots retain all disclosures. No proof or priority claim is made here.

All support predicates, sums, projector conditions, powers, finite minima, extended suprema and named statements must be concrete closed Lean definitions with the shared pinned dependency meanings. Independently review every quantifier and constructor before implementation and every actual imported meaning after implementation. Use LeanCert kernel mode, #assert_statement, #assert_trust kernel and frozen identity checks; audit OriginalAdditiveConjecture, Classification and NegativeAnswer individually as well as Target. No numerical matrix sampling, interpolation in p, large finite certificate or interval computation is needed merely to state the universal target. Formal bounds and source-correspondence proofs remain future work.
