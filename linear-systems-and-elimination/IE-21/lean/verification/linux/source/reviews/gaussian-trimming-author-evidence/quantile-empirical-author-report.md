# Quantile and empirical trimming author milestone

Author agent `reference_review`, 2026-09-22. Partial helper author evidence, not independent review or full IE-21 verification.

`QuantileTrimming.lean` proves quantile straddling for arbitrary real probability distributions via the CDF's left limit and right continuity. For nonnegative mean-one variables it proves a nonnegative threshold at most `1/(1-θ)`. Fractional mass on an atom gives an actual measurable selector of mean θ, in [0,1], equal to one below the threshold and zero above; its weighted moment is proved equal to the frozen population dual. Thus atomlessness is unnecessary, not a substituted hypothesis.

`EmpiricalTrimming.lean` proves an attained threshold in [0,L] whenever at least k observations are at most L, then the exact deterministic inequality `|finiteTrim k y − Σ y_i w_i| ≤ L |k−Σ w_i|` for a threshold-aligned fractional selector. It uses the actual exact-cardinality finite minimum and handles k=0 and ties. This is the deterministic input needed to retain the source's five-tail pointwise concentration bound. It does not yet prove that probability bound.

Separate fresh local-module builds and public axiom audits passed: four quantile helpers and three empirical helpers, all with exactly the standard permitted three foundational axioms. All dependency source hashes are in the corresponding JSON receipts. Cached pinned dependencies were reused; LeanCert and Comparator have not run on these modules. Sources are now stable for independent review. No boundary, metadata, status, or Solution file was changed.

SHA256:

```text
c1601c196a8c6c08f187ee0b6eb699ea1781b34ab0a639c0e1e6bd3da09eb098  NLA/IE21/QuantileTrimming.lean
3e634d650b5f7d066457d9eccd8406ae0945c1774890282b2a5ac8cf58000267  NLA/IE21/EmpiricalTrimming.lean
fce653d1b4b34543e45f9cdf8f450350c0c8efd677964bb030732b5b0731ed85  NLA/IE21/PopulationTrimming.lean
07519921bf6d3ca9919afbf0287e572238a80d310d0467f1c1d30b1e2aeef038  NLA/IE21/FiniteTrimming.lean
e2c047e21513e7665579e61d01ba0f64a4607baf1739d3962a28d9d298cce0f3  reviews/gaussian-trimming-author-evidence/QuantileAxioms.lean
12db409d8433eaddb97dd8e4ddb82b76ae98d04c4be93cf45384192fbf286878  reviews/gaussian-trimming-author-evidence/quantile-typecheck.py
e08c40f3513ded99c2bbb137e18eb6d2e5dfaf3225dce631e8fa6ff030b807d5  reviews/gaussian-trimming-author-evidence/quantile-typecheck.log
b266b775779b14cb068e5c4b31f008340babb8e1ee7c48529852011966dd3057  reviews/gaussian-trimming-author-evidence/quantile-author-evidence.json
3e408932b607478e5648f265945278b85e5864787a83098fd2ce2ad302d9b5a1  reviews/gaussian-trimming-author-evidence/EmpiricalAxioms.lean
d679b70cce0ce05bf19a805a9a1ac8a958be55fd48431124893b77cb774afb5a  reviews/gaussian-trimming-author-evidence/empirical-typecheck.py
0fc91b907d045b641ad39b037a20aebcebd00776531bfa674104cf499fb62628  reviews/gaussian-trimming-author-evidence/empirical-typecheck.log
782fff4f03163877ad999425ce19dd35a8115ac0f3ba4f23cc11df4649b548f4  reviews/gaussian-trimming-author-evidence/empirical-author-evidence.json
```
