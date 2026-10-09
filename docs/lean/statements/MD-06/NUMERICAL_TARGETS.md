# MD-06 exact mathematical and numerical specification

Author: OpenAI Codex AI agent `/root/infra_audit`, 2026-09-28. Preimplementation specification: two independent approvals must precede code. Permanent ID `MD-06`; canonical path `matrix-discrepancy-and-optimization/MD-06/README.md`; campaign base `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`. The full canonical page is preserved byte-for-byte as `ORIGINAL.md`, SHA-256 `b51eaf3dd9c4f4a806ca01125997909a625af86477d3daad5a7e095746c3f039`. `source-lock.json` also binds the original TeX, old formalization and retained resolution manuscript. No canonical status, ID, statement or attribution changes.

## Preserve the original conjecture separately from its negative answer

The canonical question is literally whether a specified probability tends to **one**. It is not an unspecified classification of limiting probabilities. The new `Target : Prop` must therefore be the original limit-one proposition, even though the retained manuscript refutes it. A false proposition can and must still be stated faithfully. It must not be replaced by the limit-zero resolution, nor conjoined with its negation.

Separately named closed definitions `NegativeResolution : Prop` and `QuantitativeResolution : Prop` will state the retained answer and its explicit stability strengthening. Both require the same statement/axiom/trust checks and final independent correspondence review as Target. Their presence is not a proof. The old `CompleteTarget` concerned the resolution instead of the original conjecture; that historical scope is recorded rather than silently transferred to the canonical new Target.

## Concrete graph probability space

For each natural `n`, use actual `SimpleGraph (Fin n)`: undirected labelled simple graphs, with no loops or multiple edges. Cubic means every vertex has exactly three neighbors. One may use the inspected `SimpleGraph.IsRegularOfDegree 3` or the definition `forall i, card {j : Fin n | G.Adj i j}=3`. `SimpleGraph (Fin n)` is a finite type in the pinned library. Its cubic subtype is finite as well. Do not quotient by graph isomorphism, restrict to connected graphs, or change to a configuration/multigraph model.

Uniform probability of any concrete predicate `P` on these graphs is the exact real ratio

```
Probability(n,P) =
  (card {G : SimpleGraph (Fin n) // Cubic(G) and P(G)} : Real) /
  (card {G : SimpleGraph (Fin n) // Cubic(G)} : Real).
```

The cardinalities are finite-type cardinalities, using classical decidability for the event when necessary; this is the actual finite uniform law and requires no computable decision procedure for a local-minimum event. An equivalent normalized finite counting measure is acceptable. No arbitrary probability functional is permitted. The denominator is positive for every even `n>=4`: the labelled cycle edges together with opposite-vertex matching give a simple cubic graph (for `n=4` this is K4). Thus no totalized zero denominator occurs in the target domain.

Index the required sequence by `size(k)=2*(k+2)`, for all natural `k`. This enumerates every even size at least four exactly once and tends to infinity. Limits along `k -> infinity` are precisely the canonical even-subsequence limits. No rate, lower cutoff depending on an event, or restriction to a subsequence of convenient graph sizes is introduced.

## Actual torus, energy and local minima

Use `Phase(n) = Fin n -> Real.Angle`, with the finite product of its usual quotient topology. The inspected pinned `Real.Angle` is literally `AddCircle (2*Real.pi)`, the real quotient modulo integer multiples of `2*pi`. Its `Real.Angle.cos` and `sin` are the periodic lifts of the ordinary real functions; on a real representative they equal `Real.cos` and `Real.sin`. No arbitrary phase carrier or topology is allowed.

Define the real energy by counting each unordered edge once:

```
Energy(G,theta) = sum_i sum_j
  if i<j and G.Adj i j then 1 - Angle.cos(theta_i-theta_j) else 0.
```

Here the comparison on `Fin n` is the usual label order. It merely chooses an orientation for each unordered edge; the cosine is even, so the value is label-invariant. Using a sum over the actual unordered edge finset is equivalent if its multiplicity is inspected. Do not omit edges or introduce the factor of two from an unrestricted adjacency sum.

Synchronization means `forall i j, theta_i=theta_j` **in Real.Angle**, hence equality modulo `2*pi` across every pair of vertices, including different connected components. It is not just constancy along edges. Local minimum is the actual `IsLocalMin (Energy G) theta`: some neighborhood of theta in the whole product torus has energy at least its energy. This is the pinned non-strict local-minimum predicate, not global minimality, stationarity, a positive-Hessian test or strict local minimality. Common rotation symmetry is not quotiented away in Target.

Let `AllSynchronized(G)` mean `forall theta : Phase(n), IsLocalMin (Energy G) theta -> Synchronized(theta)`. The original closed proposition is exactly

```
Target := Tendsto (fun k => Probability(size(k),AllSynchronized)) atTop (nhds (1 : Real)).
```

This retains every local minimum; no random initialization, basin-of-attraction probability, chosen critical point, connected-graph promise or simulation threshold replaces the event.

## Separately named answer and exact stability constants

`NegativeResolution` uses the **identical** graph law, phase space, event and sequence, but concludes the real probability tends to zero. It is the manuscript's negative answer, not the original conjecture.

For the quantitative answer define, with all finite sums concrete,

```
Gradient(G,theta)_i = sum_j (if G.Adj i j then Angle.sin(theta_i-theta_j) else 0),
HessianQuadratic(G,theta,z) = sum_i sum_j
  (if i<j and G.Adj i j then
     Angle.cos(theta_i-theta_j) * (z_i-z_j)^2 else 0),
MeanZero(z) iff sum_i z_i=0,
NormSq(z) = sum_i z_i^2,
```

where `z : Fin n -> Real` is a real tangent direction, **not a phase vector modulo 2*pi**. These are the exact gradient and Hessian quadratic form of the energy in periodic real coordinates. In particular, the Hessian has no missing or extra factor of two.

Let `StableNonsynchronized(G)` assert existence of one `theta : Phase(n)` such that all of the following hold together:

1. `IsLocalMin (Energy G) theta` and `not Synchronized(theta)`.
2. Every gradient coordinate equals zero exactly.
3. For every adjacent pair, `1/32 < Angle.cos(theta_i-theta_j)`.
4. For every real direction z with `sum_i z_i=0`, `(1/320)*sum_i z_i^2 <= HessianQuadratic(G,theta,z)`.

The strict cosine version preserves the older stronger resolution statement: the manuscript proves edge cosines at least `c0/2` with `c0>1/16`, hence strictly greater than `1/32`. It implies the canonical resolution banner's weak `>=1/32` formulation. The Hessian lower bound is weak `>=1/320`, includes the zero direction and uses a single absolute constant independent of n,G,theta,z. Local minimality is explicit so a missing derivative-to-local-minimum correspondence cannot silently change the advertised event.

`QuantitativeResolution` is exactly `Tendsto (fun k => Probability(size(k),StableNonsynchronized)) atTop (nhds (1 : Real))`. There is no finite-n success threshold or convergence rate in the source. The event is existential in theta for each graph, not a supplied selection algorithm or a probability over phases. Target, NegativeResolution and QuantitativeResolution must remain separately exported propositions with clear labels.

## Retained supporting numerical and quantifier record

The following belong to the existing proof record rather than to the original limit-one Target. Preserve them in this specification; no proof of them is prerequisite merely to state the three propositions above.

The small-gradient certificate takes every finite connected graph with at least two vertices, real `gamma>0`, real `c>0`, Laplacian gap at least gamma, and a real lift phi whose edge cosines are at least c. If its Euclidean gradient norm is strictly less than `c^2*gamma/(4*sqrt(2))`, it produces a mean-zero correction h with `||h||<c/(2*sqrt(2))`; phi+h is an exact critical local minimum, its edge cosines are at least c/2, and its Hessian on mean-zero real directions is at least `(c*gamma/2)*||z||^2`. No strict minimum on the full rotation-invariant torus is asserted.

For each integer `R>=4`, `F_R(t)=3*asin(t)+2*sum_{j=1}^{R-1} asin(t/2^j)` has a unique root `t_R` in `(0,1)` with value `2*pi`, and `t_R>1/2`. Set `c0=sqrt(1-t_4^2)>1/16`, `delta_j=asin(t_R/2^j)`, `a_j=sum_{s=j}^{R-1}delta_s` and `a_R=0`. The exact identities are `2*a_0+delta_0=2*pi`, `sin(2*a_0)=-t_R`, `cos(2*a_0)=sqrt(1-t_R^2)>=c0`.

For every positive cycle length ell divisible by four and `gamma>0`, choose an integer `R>=4` with `2^(R-1)>32*ell/(c0^4*gamma^2)`. A connected cubic graph with Laplacian gap at least gamma and a clean radius-R neighborhood of that cycle has the stated nonsynchronized minimum, edge cosine at least c0/2 and Hessian lower bound c0*gamma/2. Clean means the induced distance-at-most-R neighborhood is unicyclic with that unique cycle. The localized profile's squared gradient norm is exactly `ell*t_R^2*2^(1-R)`. At gamma=1/10 one permitted explicit choice is `R=29+ceil(log_2 ell)`.

The random-graph inputs fix ell,R **before** taking even n to infinity. The gap-at-least-1/10 event has probability tending to one; fixed-ell cycle counts have Poisson mean `2^ell/(2*ell)`; the chance of an ell-cycle with a nonclean R-neighborhood is `O_(ell,R)(n^-1)`. No independence of these events is assumed. The resulting limsup bound is `exp(-2^ell/(2*ell))` for each fixed positive ell divisible by four; only afterward does ell tend to infinity. These statements do not give uniform estimates for growing ell or R.

The source's rational 20- and 500-vertex examples and symbolic finite gadget are supplementary existence diagnostics, not the asymptotic target. They need not be rerun for a statement. The source archive's disclosed missing `analytic_gadget.py` files remain a provenance limitation; no new proof claim is based on them.

## Old scope gaps, credit and checking

The old `lean/Definitions.lean` quantified an arbitrary `ScalarModel` and `Semantics` carrying unspecified graph/phase types, probability, even-limit predicates, local minima, derivatives and norm. `Challenge.lean` only conjoined two such contracts; `Solution.lean` projected an already assumed nonsynchronized critical point from a strong-event hypothesis. None supplies the actual graph law, torus topology or analytic semantics. A new closed target must not import those abstract records or substitute arbitrary interpretations for them.

Matthew J. Colbrook, University of Cambridge, retains credit for the negative resolution; the full source and historical conjecture credit remain in ORIGINAL. The reviewed manuscript raw-byte hash is `3804a3121d5733665bde98008a8f5226b4d30afe945aec3d712f2de07b9200b9`. Informal AI-assisted/agent-review disclosures remain unchanged.

Use the shared pinned Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. Final reviewers must inspect actual finite graph/cardinality, Angle topology/trigonometry, local-minimum and limit APIs. All three exported propositions require `#assert_statement` and `#assert_trust kernel`; no target axiom or theorem proof is claimed. Frozen identity and shared kernel smoke cannot establish either the false conjecture or its answer. Exact symbolic constants require no artificial numerical calculation.
