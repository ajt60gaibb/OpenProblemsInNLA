# RE-06 author support: exact SVD and worst-case count

This author implementation supplies two of the six frozen public exports. It does not prove Gaussian success, OriginalClaim, ExplicitClaim or Target, and is not an independent review or a full verification claim. Sidney Holden retains authorship of the preserved mathematical manuscript. `/root/re06_counts` implemented this Lean support.

The unchanged actual `exactSVD` is valid for every rectangular matrix, including empty dimensions. Its wrapper uses only the byte-exact separately reviewed TR-04 SVDCore/SVDTotal from immutable source `653b8f1641415f4160811648ff3e23889ba2e136`. The frozen pre-proof packet preserves those source bytes and their separate review provenance. Existence is connected to the actual classical choice branch; it is not a new public assumption.

The actual committed query list has length `min n (s+k+ell)`, for every real stream. The arithmetic proof establishes `r <= 3 sqrt(log(2M))` from the actual integer logarithm and square-root definitions. Uniform real-ceiling bounds give `s <= 97 r/eta^2`, `k <= 259 r/eta`, and `ell <= 67081 r/eta^2`, with `eta=epsilon/4`. Hence the sum is at most `67437 r/eta^2`, and the final coefficient is `3236976 <= 4000000`. The proof is independent of success, matrix values, rank, Gaussian samples, or a probabilistic event. It preserves the exact public positive-dimension/accuracy header.

`CountAudit.lean` consumes both literal frozen public types, checks both declarations and all 13 arithmetic-support declarations are actual theorems, asserts kernel trust, and proves live/Reviewed Target identity by reflexivity. The clean replay builds fresh own project objects against the frozen pins and removes them after checking; three negative controls reject two theorem holes, a definition alias, and a custom axiom. Retained development failures remain diagnostic evidence. The final source has no mathematical holes or new axioms.

Reproduction from a checkout containing the source freeze:

```bash
python3 reproduce_counts.py --repo /absolute/checkout --output /absolute/new-output
```

Pass `--lean` and `--packages` to select the exact pinned runtime and already populated dependency cache. This author Mac replay is neither a Linux CI receipt nor a Comparator receipt. Both independent source/package reviews and full problem evidence remain required.

The completed fresh replay passed **15/15 expected outcomes**: 12 fresh project/audit builds and three genuine rejection commands. Both public theorem axiom lists are exactly the standard three axioms. A separate input audit verifies all 49 published and nine supplementary reuse snapshot hashes, and the 217-entry registry remains byte-identical.
