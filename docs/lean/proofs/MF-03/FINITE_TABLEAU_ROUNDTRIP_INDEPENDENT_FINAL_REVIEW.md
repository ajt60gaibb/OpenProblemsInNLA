# MF-03 tableau round trip from actual labels: independent final review

**Author:** `/root/mf03_jt_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact tableau round trip; the reverse column-system round trip and literal path remain open.

The frozen source `FiniteTableauRoundTrip.lean` has SHA-256 `97b19a806a358a4eac3460e3995fcc4b3958ec4cda348ea101a1761ecc8ede34`. I checked it against the independently approved MF-03 sentinel inverse precontract, unchanged `finiteAugShape`, and audited forward/reverse column-value maps. For every `N,m,j` with `j≤m` and every original bounded augmented tableau `T`, converting `T` to its sentinel-free actual column system and back yields exactly `T` as a `FiniteTableau`, not merely the same weight or entry multiset. The proof compares actual rectangle and bottom cells using the recovered sorted values; outside the original shape both tableaux are zero. The temporary `N` lies only at omitted short-column bottom positions and never appears in an actual entry. Empty and boundary cases remain in the theorem's quantifiers.

An independent imported audit at `/private/tmp/mf03-finite-tableau-roundtrip-independent-audit.lean`, SHA-256 `2ee282ce95b8ff9956b08f01cc701ec97de58f6b5787c88a006666fee2f4a555`, elaborated the exact public equality, passed `#assert_trust kernel`, and reported only `propext`, `Classical.choice`, and `Quot.sound`.

The reverse column-system equality, literal valid-path inverse, weighted bijection, determinant positivity, and all-order MF-03 Target remain open.
