# TR-14 exact remaining proof route after retained 39-module candidate

Date: 2026-10-18. Author: OpenAI Codex AI agent `/root/solved_inventory`. Source revision: `fdb40b66425ec58e4806cee93d2aaf92a0f8597c`. All source hashes are in `input-inventory.json`. This is a proof plan after a statement/source audit, not a proof of any missing gate. No new proof bodies have been written. See `PREPROOF_STATEMENT_REVIEW_1.md` for the statement approval and the second-review condition.

## What is actually retained

The earlier 34-module gap reports are stale for this revision. Five more modules are present and freshly compile: `WidthPadding`, `BinaryFrobeniusRepresenter`, `BinaryTopRemainder`, `BinaryTopRemainderFrobenius`, and `BinaryMomentUnitInverse`.

The candidate already supplies least nonzero apolar degree `ρ`, a normalized monic polynomial `g` of degree `ρ`, invertible mode/chart transports, exact all-moment matching in `A=ℂ[t]/(g)`, a Frobenius moment functional `λ`, CRT local factors and their multiplicity sum, and an actual symmetric width witness at

```
L = (m-1)*ρ - (m-2)*s,    s = card (localRootSupport g).
```

The new inverse gate supplies a unit representer `u` with `λ(a)=τ(u*a)`, its inverse in `A`, and the top-remainder Frobenius theorem. It does not yet produce a polynomial representative, an apolar pencil, a squarefree polynomial, or a symmetric witness of width `v=D-ρ+2`. No retained module proves a nontrivial lower bound for arbitrary ordinary decompositions. Width transport, symmetric-to-ordinary absorption, zero-width facts and padding are not that lower bound.

For the final all-width theorem it suffices, in a **single** normalized chart, to show both `SymmetricWidth H v` and `SymmetricWidth H L`, and to prove `min v L ≤ w` from **every actual** `OrdinaryWidth H w`. Select the smaller symmetric witness and pad to `w`, then transport back. The reverse implication is already available. This avoids unnecessary formalization of the stronger project's original-coordinate invariant formula.

A local-upper-only substitution fails. At `m=5,n=3,D=10,ρ=4,s=2` (two double support points), the local witness has length `10`, whereas the binary upper bound is `8`. The missing ordinary lower bound has to accommodate both alternatives, all `ρ`, and all widths. Assuming `ρ≤n`, requiring mode factors to be Vandermonde, or proving only terminal single-support examples would lose the original target.

## Binary upper branch: inverse polynomial, pencil, actual moment reconstruction

1. Extract the unique degree-`<ρ` polynomial representative `b` of `u⁻¹` from `BinaryMomentUnitInverse`. Prove it is coprime to `g`, using its unit residue. For `ρ≥2`, prove `L(t^j*b)=0` for `j≤ρ-2` by reducing to `τ(t^j)=0`. Bounds are important: the products have degree at most `2ρ-3≤D`. This makes the degree-`v` homogenization of `b` apolar, where `v=D-ρ+2≥ρ`.
2. Pick `α` outside the finitely many roots of `b` and put `q=(t-α)^(v-ρ)`. Then `p=g*q` is monic of degree `v` and coprime to `b`. Exponent zero includes the balanced case `v=ρ`. For `c≠0`, `b+c*p` has exact degree `v`, so infinity is not a root. Apolarity is preserved by the pencil.
3. Prove a squarefree pencil member exists without assuming genericity: `W=b'*p-b*p'` is nonzero in characteristic zero. A repeated root `ξ` of `b+c*p` has `p(ξ)≠0`, satisfies `W(ξ)=0`, and forces the single scalar `c=-b(ξ)/p(ξ)`. There are finitely many such values. Avoid them and zero, then divide by the leading coefficient to make the chosen member monic. A coprime/degree argument or the leading coefficient of `W` proves `W≠0`; the chosen `c` must be an actual existence proof, not an unproved generic scalar.
4. Prove the proposed general Vandermonde gate below, then apply it to this actual polynomial and moment recurrence. The output is an actual frozen `SymmetricWidth`, not a supplied decomposition rule.
5. Handle `ρ=1` separately using the retained local witness (support cardinality one, hence width one), padded if needed. Here `v=D+1`; the existing apolar definition only covers degrees at most `D`, so applying it at `v` would be a type/semantic error. The general Vandermonde gate deliberately covers this case by a vacuous recurrence too.

Recommended exact reconstruction gate (approved as a sufficient proposed interface): let `D=m*(n-1)`, `h:Fin(D+1)→ℂ`, `P:Polynomial ℂ`, `0<v`, `v≤D+1`, `P.Monic`, `P.natDegree=v`, and `Squarefree P`. Assume the **full actual recurrence**

```
∀ ℓ with ℓ+v≤D, ∑ k=0..v, P.coeff k * h(ℓ+k) = 0.
```

Then prove `NLA.Statements.TR14.SymmetricWidth (Hankel h) v`. A convenient finite indexing uses `ℓ:Fin(D+1-v)` and `k:Fin(v+1)`, with the finite bound on `ℓ.val+k.val` proved from the premises. When `v=D+1`, `Fin(D+1-v)` is empty, as it should be. Exact degree and squarefreeness over ℂ give exactly `v` distinct affine roots, including possible zero roots. The square Vandermonde matrix is invertible, so solve the first `v` moments for weights. Monicity expresses the next moment in terms of previous ones, and strong induction matches through `D`. Finally the `m` equal factors `(1,β,...,β^(n-1))` reproduce `h(sum indices)` using the product-of-powers identity. The retained `MomentIndex` and frozen definitions provide the exact coordinate bridge. No conclusion about only local upper bounds or restricted widths is substituted.

## Ordinary lower branch: the actual missing major work

The source's Sections 4–5 give a concrete route. This branch is substantially larger than the retained algebra/upper-bound modules. Its gates must prove rather than assume the contextual product theorem, primitive block data, and the passage from actual arbitrary decomposition factors.

A useful concrete ambient algebra is the finite product of the truncated local factors of `g`, together with `w` copies of ℂ. Working with that explicit CRT product can avoid a general Artinian algebra classification. Keep the actual quotient `A` connected by the retained CRT equivalence.

### L1. Product subspaces, units and stabilizers

Define span-of-products for submodules of a finite commutative ℂ-algebra, its finite iterated product, scalar/unit scaling, and the unital subalgebra `Stab W={b | b*W⊆W}`. Prove monotonicity, associativity, contains-one consequences, dimension behavior under units and `Stab(partial product)≤Stab(full product)`.

For the explicit local product algebra, prove units are exactly elements with all residue coordinates nonzero. Finite hyperplane avoidance gives a unit in any subspace whose residue restrictions are all nonzero and shows units span a subspace already containing one. An alternative spanning proof uses `x+c*1` with all but finitely many scalars `c` units; it does not need a classification of all subalgebras.

### L2. Transformation lemma, with proof

For `U,V` containing units and each chosen unit `a∈U`, obtain a unital subalgebra `K_a` and subspace `T_a` with

```
a*V ≤ T_a ≤ U*V,
K_a*T_a = T_a,
finrank T_a + finrank K_a ≥ finrank U + finrank V.
```

Normalize `a=1` and one unit of `V` to one. Induct on `finrank U`. For a unit `e∈V`, set `U_e=U∩V*e⁻¹`, `V_e=V+U*e`. Dimension sum is preserved and `U_e*V_e≤U*V`. A proper `U_e` invokes induction; otherwise units span `V`, so `U*V=V` and the algebra generated by `U` stabilizes `V`. All of these statements refer to actual subspaces; a record containing the desired inequality as an unexplained field is not a proof.

This is the finite commutative specialization of [Beck–Lecouvey Lemma 4.2](https://arxiv.org/pdf/1504.02287). Their general product theorem has a subalgebra-finiteness condition; it cannot be imported without proving the relevant finiteness in the present nonreduced algebra.

### L3. Finitely many reduced subalgebras of the explicit algebra

A direct implementation can avoid an external structure theorem. Let `res:B→ₐ[ℂ]ℂ^I` be all residue coordinates. Its kernel is uniformly nilpotent. On a reduced subalgebra `K`, the restriction of `res` is injective. A subalgebra of `ℂ^I` corresponds to a partition of the finite coordinate set: coordinates are equivalent when every algebra element agrees there. Products of normalized separating elements give the indicators of the equivalence classes. Their lifts to `K` are idempotents. Every idempotent of each truncated local factor is exactly zero or one, so those lifts are the unique whole-factor indicators. Thus `K` is determined by its partition, giving finite many possible reduced subalgebras and primitive block indicators. Do not partition individual nilpotent coefficient slots; repeated-root local factors remain whole.

### L4. Contextual product inequality

Assume `B=A×ℂ^R`, a functional `Λ` whose restriction to `A` is Frobenius, subspaces `U_i` containing one, `Λ(W)=0` for `W=∏U_i`, and `π_A(∏_{k≠i}U_k)=A` for **every** `i`.

Prove each auxiliary `K_a` from L2 is reduced: a nilpotent `z` has zero ℂ-coordinates; `z*a*V*Q⊆W` and the all-but-one surjectivity force `Λ_A(z_A*a_A*A)=0`, hence `z_A=0` by Frobenius nondegeneracy and unit `a_A`. This applies to **every auxiliary algebra**, not merely to `Stab W`.

Take a basis `1,x₂,...,x_d` of `U` and the curve `a(c)=1+c*x₂+...+c^(d-1)*x_d`. All but finitely many `c` are units. L3 and infinitude of ℂ give `d` distinct parameters with the same auxiliary `K`. Vandermonde invertibility makes those units a basis of `U`; summing their `T` spaces gives `U*V`, so `K≤Stab(U*V)`. Conclude each contextual step

```
finrank W_j ≥ finrank W_(j-1) + finrank U_j - finrank (Stab W_j).
```

Also prove `Stab W` reduced directly by the same Frobenius argument and `π_A W=A`. If the final stabilizer is scalar, all partial stabilizers are scalar and the inequalities sum to `finrank W ≥ ∑i finrank U_i -(m-1)`.

### L5. Actual minimum ordinary decomposition and graph normalization

Start with the actual input `OrdinaryWidth (Hankel h) w`. Select a least width `R≤w` using that witness and `Nat.find`; thus no global witness oracle or supplied rank function is needed. Minimum-length decomposable coordinate tensors are linearly independent: a nonzero relation eliminates one summand after rescaling in one mode. Every mode functional `β_(b,i)` is nonzero, otherwise that summand can be removed.

Define the actual graph mode subspaces in `B=A×ℂ^R` by `p↦([p],(β_(b,i)(p))_b)`, and `Λ̃(a,c)=λ(a)-∑b c_b`. The ordinary coordinate identity, extended multilinearly, proves `Λ̃` annihilates their product. Finite hyperplane avoidance chooses a unit in every graph subspace, using residue evaluations and the nonzero `β` functionals. Scale to spaces `U_i` containing one and to a functional `Λ` with Frobenius `A` part and every scalar-coordinate coefficient nonzero.

Prove all-but-one `A` surjectivity from actual polynomial products: `(m-1)*(n-1)≥ρ-1`, and the powers through degree `ρ-1` span `A`. This holds when `ρ>n` too. Prove product projection onto `ℂ^R` from independence of the actual decomposable tensors, for example by the dual of the finite evaluation matrix. Coordinate functions on finite tuples suffice; an abstract tensor-product library is optional.

### L6. Reduced primitive blocks and the dimension lower bound

Use L3/L4 for `K=Stab W`. Its primitive indicators partition whole local factors and scalar factors into blocks `B_j=A_j×ℂ^(R_j)`. No block may have `A_j=0`: onto projection to the scalar factors and annihilation by `Λ` would contradict its nonzero coefficients. Consequently `ρ_j=finrank A_j≥1`, the block count `t≤s`, `∑jρ_j=ρ`, and `∑j R_j=R`.

Prove block contextual hypotheses and that `Stab(W_j)` is exactly the scalar algebra in its own block. An extra stabilizer extended by zero would contradict primitiveness of that block. Show each projected mode has dimension at least `min n ρ_j` by polynomial remainders on the block quotient, together with invertible unit scaling. Then L4 gives `finrank W_j≥m*min(n,ρ_j)-m+1`. The nonzero annihilating functional gives `finrank W_j≤ρ_j+R_j-1`. Hence

```
R_j ≥ m*min(n,ρ_j) - ρ_j - m + 2.
```

Use integer inequalities or carefully justified natural casts rather than silently subtracting naturals. If one `ρ_j≥n`, obtain `R≥D-ρ+2`. Otherwise sum the inequalities to get `R≥(m-1)*ρ-(m-2)*t≥L`. Thus `min(v,L)≤R≤w` for **every** supplied ordinary width. This is the exact unrestricted lower-bound gate needed for frozen `Target`.

## Final assembly and evidence gates

The final theorem must be a closed term of the unchanged `NLA.Statements.TR14.Target`, with `set_option leancert.trust "kernel"`, kernel trust assertion and explicit axiom output. It may depend only on proved gates. Zero moments are handled first; for nonzero moments normalize once, obtain the two actual symmetric witnesses and the all-width lower bound, choose the smaller witness, pad, and undo the chart. Preserve all original IDs, pages, mathematical credits and source documents.

Before claiming full verification: independently review the final proof and reuse scope; materialize an exact copied import closure in the canonical package; freeze live/frozen/challenge definitions and compare them; provide exact source locks and complete local replay; validate metadata and export coverage; then run the actual pinned Linux CI and Comparator with the full target export. Retained 39-module compilation establishes none of those final claims. Existing numerical metadata's historical preimplementation prose should not be mistaken for a current full-proof claim.
