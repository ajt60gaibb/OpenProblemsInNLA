# MF-03 uniform columns to the original tableau: independent final review

**Author:** `/root/mf03_jt_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this exact forward tableau map; the inverse and weighted bijection remain open.

The frozen source `FiniteUniformTableau.lean` has SHA-256 `c34cf287c96eb26c77156c7073b750c9b01993c75dc71cea202a68768e7540cf`. I checked its mathematical statement and implementation against the independently approved uniform-sentinel precontract, original `FiniteColumnSystem`, frozen `finiteAugShape`, and `FiniteTableau`. The entry function takes the sorted uniform-column label at every actual cell and zero elsewhere. The shape is exactly the `m×m` rectangle plus bottom cells in columns `p<min j m`; in a short column, the temporary sentinel `N` is the excluded bottom value, so no sentinel can be an entry or a cosine factor. The proof establishes weak rows across arbitrary column gaps, strict columns, and `<N` on every cell, including `m=0`, `j=0`, `j=m`, and empty tableau types. The source retains the supplied path-derived column system and does not assert an inverse or weighted-sum identity.

An independent imported audit at `/private/tmp/mf03-finite-uniform-tableau-independent-audit.lean`, SHA-256 `f71281debb2e663cd0409b40267a5bc6fa4325158f2b0d97f4f4a4712edc7ba5`, elaborated the exact public row, cell, strictness, and tableau-map signatures, passed `#assert_trust kernel`, and reported only `propext`, `Classical.choice`, and `Quot.sound`.

The tableau-to-column and column-to-path inverses, factor-weight preservation, determinant positivity, and all-order MF-03 `Target` remain open.
