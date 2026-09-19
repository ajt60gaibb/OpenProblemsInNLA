# PF-03 exact statement draft

This is a translation of the independently reviewed 25-contract mathematical
plan, not a completed formalization. No Lean execution or new mathematical
resolution is claimed. The exact-source header review gate is still pending.

The complete target is an unconditional counterexample to rational nonnegative
Gram factorability on the completely positive boundary. The final assertion
quantifies over every order at least five and every positive finite factor
width; frontier uses the real symmetric-matrix topology.

Sidney Holden retains the original mathematical and seed-data authorship,
Center for Computational Biology, Flatiron Institute, Simons Foundation.
George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, contributes formalization and proof
engineering with substantial Codex assistance. The present statement author
is /root/recover_published_coverage and cannot serve as its own independent
statement referee.

## Files and pending execution

- NLA/PF03/Definitions.lean contains only transparent definitions. Its two
  subtype constructors use existing generic library symmetry lemmas; no
  substantive PF-03 theorem is assumed or implemented.
- Challenge.lean contains exactly 25 deliberately unproved reference contracts.
  A future Solution must never import it.
- comparator.json lists all 25 contracts, no replaceable definitions, and
  only Lean's three standard foundational axioms.
- NUMERICAL_TARGETS.md fixes all numerical and universal obligations.
- generate_raw_data.py is a pure literal translator prepared for root review.
  Its author did not run it. Root must inspect it, then may run
  python3 generate_raw_data.py --write to create NLA/PF03/RawData.lean.
- The Lake files pin the shared toolchain/dependencies. Challenge is the only
  current default target because no proof Solution exists. A Challenge build
  must never be counted as proof verification.

After literal generation, root alone may elaborate RawData, Definitions and
Challenge with one local Lean process, one thread, and a 4096 MiB limit. The
source author runs no compiler. Record actual logs and exact file hashes.
Then obtain two independent source reviews and freeze the reviewed bytes
before implementing any substantive proofs.

## Translation details requiring exact-source review

C15 makes the earlier prose's explicit Fourier–Motzkin construction literal:
a finite list retains zero-coefficient rows and every positive-negative pair.
C16 uses separate rational A and B blocks for retained and eliminated real
variables. This is the same arbitrary finite real projection target.

C06 fixes the seven source-selected minors at rows 0,1 and columns 0,1. C09
and C11 explicitly check the literal caches against the defined triangle,
barycentric values, generators and slice vector. C14 and C18 spell out salience,
avoiding the misleading library Pointed name.

C22 uses exactly five zero rows and a specified padded index. No exact
order-444 witness is promised. No mathematical decision has been deferred
by adding an oracle, certificate instance or extra premise to C24 or C25.
The major proof obligations C15-C17 remain genuinely unproved.

## Review guidance and examples

The source author read the retained canonical question, all 25 prose contracts,
numerical plan and both mathematical reviews. Exact-header review must apply
the repository protocol at docs/lean/REVIEW.md, pinned to Tau Ceti Review
afb424eda89e8ac96d9eb69f6a88972055a4cd1b. This is manual rubric application,
not an official Tau Ceti service run or human peer review.

The separate transparent Definitions/Challenge pattern follows the previously
consulted Schiffer revision 2938e277969c329caf154e48a3d8823f3635c7f1 and
Forsythe revision 8d1b0c0545a77b40245e84705aa7d273e6c81e62. Their mathematical
theorems are not imported. A final successful publication will additionally
need two complete nonauthor proof reviews, actual local Lean evidence, exact
published-source non-root Linux Comparator/kernel/sandbox checks, and truthful
schema-valid formalization.yaml. None of those later gates is satisfied here.
