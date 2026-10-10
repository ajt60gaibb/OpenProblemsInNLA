# MF-03 tableau to exact original column system: independent final review

**Author:** `/root/mf03_jt_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the sentinel-free column-system map; literal inverse paths remain open.

The frozen source `FiniteTableauColumnSystem.lean` has SHA-256 `1929b346a116a038fdc939a237839fae2657f225492e1e6a1fd7cb9e51cd1bd6`. I checked it against the approved MF-03 sentinel/path precontract, frozen `FiniteColumnSystem`, and independently audited tableau label-set and cut gates. For every bounded original augmented tableau and every `j≤m`, the map sets `D.labels p` to exactly the actual column labels after erasing temporary `N`. Its `label_lt` proves every factor label is `<N`; its `card_eq` preserves lengths `m+1` for `p<j` and `m` for `p≥j`; its `noncollision` is the original one-gap suffix inequality at every `q≤N`. No sentinel enters a path factor, no tableau shape or endpoint changes, and empty cases remain in scope. This is the reverse data map, not yet a path-chain inverse.

An independent imported audit at `/private/tmp/mf03-finite-tableau-column-system-independent-audit.lean`, SHA-256 `2fee2a56710a1588851a725fc4c6be42a40adb5a5b801c66f2e4af909806aac4`, elaborated the exact map and all three record fields, passed `#assert_trust kernel`, and reported only `propext`, `Classical.choice`, and `Quot.sound`.

The two-sided tableau/column-system inverse, literal path reconstruction, weighted-sum bijection, determinant positivity, and all-order MF-03 Target remain open.
