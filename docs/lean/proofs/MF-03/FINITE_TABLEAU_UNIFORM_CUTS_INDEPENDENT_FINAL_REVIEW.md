# MF-03 original noncollision cuts from tableau rows: independent final review

**Author:** `/root/mf03_jt_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact one-gap cut inequality; the path inverse remains open.

The frozen source `FiniteTableauUniformCuts.lean` has SHA-256 `828c45802180abebcde62934338ec6bf32567693cd5a78206c45ab89c4965c8d`. I checked it against the independently approved sentinel/path precontract, frozen `finiteLabelSuffix`, original augmented tableau, and audited uniform and actual label sets. The strictly sorted temporary column's image preserves every suffix count. Weak tableau rows give equal-length suffix dominance. For every cut `q≤N`, erasing the sentinel subtracts one suffix label **exactly** from each short column `p≥j`. Hence adjacent actual columns satisfy the source's original unsimplified noncollision inequality with allowance `1` only at the unique crossing `p+1=j`, and `0` otherwise. The proof preserves the factor-label cutoff, column order, all empty cases, and `j=0,m`; no path is yet constructed.

An independent imported audit at `/private/tmp/mf03-finite-tableau-uniform-cuts-independent-audit.lean`, SHA-256 `943c6a5757f74a295110d062a485be8dfe124fe8e1abe6c0984685458a73ecb2`, elaborated all four exact public signatures, passed `#assert_trust kernel`, and reported only `propext`, `Classical.choice`, and `Quot.sound`.

The column-system wrapper, literal inverse path, weighted bijection, determinant positivity, and full all-order MF-03 Target remain open.
