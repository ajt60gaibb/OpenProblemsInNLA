# MF-03 tableau and actual column-system equivalence: independent final review

**Author:** `/root/mf03_jt_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact equivalence; literal valid-chain equivalence remains open.

The frozen source `FiniteTableauColumnEquiv.lean` has SHA-256 `aa901f6b28f098a82e3ea4dbde2220350919ab48109559c07198663b835d1a1e`. Its forward map is the audited actual-label column-system-to-tableau construction on the unchanged `finiteAugShape m j`; its inverse is the audited tableau-to-actual-label construction. The two separately kernel-proved round-trip identities supply exactly the `Equiv` laws, for every `N,m,j` with `j≤m`. It adds no new endpoint, sentinel cell, factor, or premise.

The independent imported exact-signature audit `/private/tmp/mf03-finite-tableau-column-equiv-independent-audit.lean`, SHA-256 `d6c8433c69472818f5c943c4aa7d0510be3b12bdd3a93acdeed25491fdc154c0`, passed pinned LeanCert kernel and reported only `propext`, `Classical.choice`, and `Quot.sound`. The literal path-chain inverse, weight transport, determinant/tableau equality, and full MF-03 Target remain open.
