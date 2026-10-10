# MF-03 reverse column-system round trip: independent final review

**Author:** `/root/mf03_jt_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact column-system identity; literal path-chain inverse remains open.

The frozen source `FiniteColumnUniformInverse.lean` has SHA-256 `813761d2018fcd3ee8e4e3cdadff0b4a86c8511de1b933cbe1a6bccdaa9e196c`. I checked it against the independently approved MF-03 sentinel inverse precontract, unchanged augmented tableau, frozen `FiniteColumnSystem`, and audited forward tableau map. The forward tableau's temporary uniform value equals the original sorted uniform label at **every** row, including excluded short bottoms where both equal sentinel `N`. Its uniform image is the original augmented set; erasing only `N` recovers each original actual `D.labels p`. Equality of all actual label sets yields equality of the full column-system records, so converting `D` to its tableau and back is exactly the identity. No path factor or tableau cell receives the sentinel, and the theorem covers empty and endpoint cases. Combined with the audited tableau round trip, these are both directions of the actual tableau/column-system bijection, though the literal path-chain reconstruction remains open.

An independent imported audit at `/private/tmp/mf03-finite-column-uniform-inverse-independent-audit.lean`, SHA-256 `9c79c3f959043cb992925cec43e4aed1489b43a43a362811749fc39d3bc16f6c`, elaborated all five exact public signatures, passed `#assert_trust kernel`, and reported only `propext`, `Classical.choice`, and `Quot.sound`.

Packaging the equivalence, literal inverse valid path, weighted-sum transport, determinant positivity, and full all-order MF-03 Target remain open.
