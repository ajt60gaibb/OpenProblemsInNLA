# Independent MatrixInfra port review

Reviewer: source_statement_author, independent of the port implementation.

Approved port hashes:
- Basic.lean: b92a6b22835439dc84f00eae91155c4ed2d4f0e2ae9346be76a1494d877aa69c.
- CourantFischer.lean: 30aa19e792d92677f4a77277cef765ed82c9524d6f7d8a82b6f4b2726ac4db05.

The source and provenance refer to [YuanheZ/lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory), commit d0f506f0a695018265dccb33bcb05e2f5ca1c876, under Apache-2.0. The independently computed source hashes match the provenance manifest: Basic c31f4ab9074f768b5d44b8dcc2ddf6b550ca5bc767174f4c7ac9bf649f5afd22 and CourantFischer 32d4f99e48b8bc5a587490c8024573548a32ed464f6ca6ee9ebc6b7ffd4e98e6.

The complete source-port diffs preserve every mathematical declaration and hypothesis. Basic adds only an explicit rewrite of the true branch after the equal-index substitution in the orthonormal-left-singular-vector proof. CourantFischer has no proof changes. The remaining changes are the relocated import, source attribution, kernel trust option, and per-declaration audit commands. There are no added axioms, sorry/admit placeholders, native_decide, unsafe/extern implementations, or custom elaborators.

I independently recompiled both port files under the pinned Lean 4.33.1 and existing package cache, into a separate temporary local build directory. All 50 Basic declarations and 80 CourantFischer declarations passed the included kernel trust assertions. The transitive axiom output contains only propext, Classical.choice and Quot.sound. The log is /private/tmp/ie06-matrix-infra-independent-check.log. Existing style warnings in CourantFischer do not affect proof trust.

The adoption is approved as a faithful checked source port. This review is about declaration fidelity and kernel trust; it does not claim that these general SVD and min–max theorems alone establish the manuscript's separate stacking or probabilistic estimates.
