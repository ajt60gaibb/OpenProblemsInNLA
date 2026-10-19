# TR-14 actual contextual iteration and ordinary graph units — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I authored neither new source. **APPROVE these exact conditional gates.** They do not construct the primitive tensor blocks or establish the full ordinary lower bound/Target.

| Module | SHA-256 |
| --- | --- |
| `ContextualIteration` | `f3414dc6a43fa95c265b2097d90cd3024001f7c169e2e5f8d2ccc506b6991f5f` |
| `OrdinaryGraphUnits` | `0ebccc47855ecb230401740757ca5756814a0a2613f3d44d2e36663ef80cecba` |

`ContextualIteration` treats the actual list positions: the all-but-one projection at a factor is the product of its take-prefix and drop-tail, with the indexed factor omitted exactly once. Products of one-containing spaces contain one, including an empty scalar-one prefix. For each prefix/factor/tail split, the proved contextual product theorem applies to the prefix and chosen factor using the same final annihilated product as W and the actual tail as Q. Its current prefix stabilizer acts on the final product by the proved multiplication-stabilizer inclusion, so every step is bounded by that actual final stabilizer dimension. Induction extends a nonempty prefix by one factor, preserving the exact coefficient length−1. Starting with a singleton gives the correct zero stabilizer coefficient. The corollary uses the explicit final stabilizer dimension≤1; it does not assume primitive block existence or scalar stabilizers. Frobenius nondegeneracy, annihilation and every all-but-one full first projection remain visible application conditions.

`OrdinaryGraphUnits` proves actual unit existence without requiring any ordinary factor's constant coordinate to be nonzero. Independence of genuine ordinary summand functions makes each mode functional nonzero. Finite dual-hyperplane avoidance chooses an actual p0 where all those functionals are nonzero. An explicitly provided p1 maps to one in the algebra. On p0+c*p1, the quotient component is a unit outside the finite spectrum of −φ(p0), while each scalar component has at most one forbidden affine-zero parameter (or no zero when its slope vanishes). Avoiding that finite union supplies one actual complex scalar and hence an actual unit of the product algebra lying in the genuine graph range. Only membership of one in the quotient map's range, actual summand independence and finite-dimensional commutative complex algebra are required. Scalar-coordinate families may be empty and individual original factor entries may vanish. No generic-coordinate or graph-unit oracle is supplied.

The two lemmas remain separate support gates: later code must apply unit scaling to obtain one-containing actual graph factors, prove all list complement projections with the real quotient mode product-span theorem, and construct actual corner/block stabilizer bounds. This review does not substitute those conditions for the all-tensor Target.

Independent fresh immutable verification passed **19 Lean commands**: 18 actual local sources plus a separate consumer. It audits **76 explicit declarations**, including **68 theorem/lemma constants**, their actual theorem kind, LeanCert kernel trust and transitive printed axiom closure. Only propext, Classical.choice, Quot.sound occur. All source bytes and all ten dependency pins/tracked trees pass before/after. Every project object is freshly rebuilt in a private output prefix excluding campaign project objects; pinned dependency objects are reused.

Reproduce from the repository root:

```bash
python3 docs/lean/proofs/TR-14/verification/check-iteration-and-graph-units.py \
  --top ContextualIteration OrdinaryGraphUnits \
  --evidence-name iteration-and-graph-units-review-3
```

Exact sources, consumer, driver/compiler hashes and raw logs are in [verification/iteration-and-graph-units-review-3/](verification/iteration-and-graph-units-review-3/). Previously approved contextual, unit-span/avoidance, minimum-decomposition and ordinary-graph semantics retain their separate reports. No proof, original target, permanent ID or canonical page was edited. This is independent source review and local macOS Lean4.33.1 evidence, not a full lower-bound/Target proof, Linux Comparator receipt, external human peer review or source-author endorsement.
