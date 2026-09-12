# MI-03 Lean statement package

**Statements only; proof not implemented.** The complete original odd-summand sharp-constant question is specified in [Definitions](NLA/MI03/Definitions.lean), the eight [Challenge declarations](Challenge.lean), [exact numerical targets](NUMERICAL_TARGETS.md) and [source correspondence](SOURCE_MAP.md). Two independent statement approvals must precede implementation. No Lean-verified status or Linux result is claimed.

Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI assistance. Mathematical proof: **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Original conjecture and prior-bound credit remains Bourin and Lee.

The universal bound retains every positive matrix dimension and every tuple of complex contractions in the actual Euclidean operator norm. The sharp constant is the actual real infimum of that complete admissible set. The planned proof establishes a least admissible constant k/4 for every k≥2 and therefore the original statement for every odd k≥3.

The source's exact positive-square decomposition gives the full upper bound. The actual complex roots of unity and two-dimensional outer-product construction give sharpness for every k. Matrix powers, principal positive square roots, PSD order, Euclidean norms, finite sums and the real infimum retain their library meanings. The additional three-dimensional Hermitian extremizers are outside the eight formal exports.

This is an exact symbolic argument. **LeanCert is planned for explicit kernel trust auditing; no numerical interval certificate is needed or claimed.** Pin Lean **4.33.1**, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, with all transitive pins in [lake-manifest.json](lake-manifest.json).

From this directory, statement elaboration is:

```
lake build Challenge
```

The eight deliberate Challenge placeholders prove nothing and are isolated from the future Solution. The [Comparator configuration](comparator.json) lists all eight intended exports with no definition exceptions and only `propext`, `Classical.choice` and `Quot.sound`. Actual proof implementation, two independent final reviews, real Linux Comparator/default-kernel execution, truthful v0.4 `formalization.yaml` and individual upstream publication remain later gates.

The repository's [Lean workflow](../../../docs/lean/README.md), [referee protocol](../../../docs/lean/REVIEW.md) and [harness](../../../tools/lean/HARNESS.md) apply. Existing pinned dependency caches may be reused for local macOS elaboration; that is not a Linux run or a full rebuild of all Mathlib sources. Original canonical pages and mathematical sources remain unchanged, with canonical MI-03 still Solved.
