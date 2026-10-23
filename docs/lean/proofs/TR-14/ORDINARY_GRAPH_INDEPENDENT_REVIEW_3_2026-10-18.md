# TR-14 actual arbitrary ordinary-factor graph spaces — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I authored no TR-14 source. **APPROVE `OrdinaryGraph.lean` at SHA-256 `fa3cee7e642538effca450cdb15e40bf89e3826a113d45310c816f2be00664e9`.** This establishes actual graph/projection/annihilation gates, not a full lower bound or Target proof.

The mode forms are the literal complex bilinear dual coordinate sums of arbitrary ordinary factor vectors, with no conjugation. Evaluation on a coordinate basis vector recovers the actual factor entry. Minimum-summand independence excludes an identically zero whole mode form; individual entries may still vanish. Nothing restricts these arbitrary ordinary vectors to Hankel, symmetric or Vandermonde vectors.

For any actual linear map φ into the commutative quotient algebra A, the graph space is exactly the range of p↦(φ(p), (β_jk(p))_j). Its first projection equals range(φ) by explicit preimages, without asserting that this individual mode range is already the whole quotient. The generic finite product-of-ranges theorem identifies the genuine submodule product with the span of actual pure-product images. It also handles the empty product as the scalar-one subspace.

Independence of the actual rank-one coordinate functions makes them independent rows of the finite coefficient matrix indexed by summands and tensor-coordinate tuples. Its rank is exactly the summand count, so its actual column span is the entire scalar-coordinate space. Every such column is the second projection of an actual product of graph generators, using each tensor coordinate's mode basis vector. Therefore the product graph space really projects onto all scalar coordinates. This is a rank calculation for the evaluated summand functions; it does not replace the tensor's ordinary rank with a flattening rank or assume the desired tensor lower bound.

The ordinary decomposition's multilinear identity is obtained by finite coordinate expansion, exchanging sums and expanding a product of sums. The graph functional is exactly Λ(first component) minus the sum of actual scalar coordinates. Given the explicit quotient moment-pairing premise, it vanishes on every pure graph product by that identity and hence on the full product span. The identity is required for every collection of mode test vectors; no generic choice or restricted test family is substituted. The quotient-mode pairing premise must still be instantiated with the actual normalized moment functional by later code.

Independent immutable verification passed **seven Lean commands**: six actual local sources and a separate consumer. It audits **38 explicit declarations**, including **30 theorem/lemma constants**, actual theorem kind, LeanCert kernel trust and transitive printed axiom closure. Only propext, Classical.choice, Quot.sound occur. All source bytes and ten dependency pins/tracked trees pass before/after. Every local object is built in a fresh private output prefix excluding campaign project objects; pinned cached dependency objects alone are reused.

Reproduce from the repository root:

```bash
python3 docs/lean/proofs/TR-14/verification/check-ordinary-graph.py \
  --top OrdinaryGraph --evidence-name ordinary-graph-review-3
```

The exact driver, source/consumer snapshots, hashes and raw logs are in [verification/ordinary-graph-review-3/](verification/ordinary-graph-review-3/). The independent minimum-ordinary and product-stabilizer source reviews remain separate. No proof, statement, permanent ID or canonical page was edited for this audit. This is local macOS Lean4.33.1 kernel evidence, not a full product/block lower bound, Target proof, Linux Comparator receipt, external human peer review or source-author endorsement.
