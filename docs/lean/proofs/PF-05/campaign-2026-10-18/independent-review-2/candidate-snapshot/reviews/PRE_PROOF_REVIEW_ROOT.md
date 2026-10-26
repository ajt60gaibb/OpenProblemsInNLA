# PF-05 independent pre-proof statement review

**Phase:** Before proof implementation, 16 October 2026.  
**Reviewer:** Codex agent `/root`, independent of the agent that prepared this PF-05 project packet.  
**Verdict:** APPROVE the exact Challenge boundary below. This is a statement review, not a proof verification.

## Reviewed source identity

The canonical `nonnegative-and-positive-factorizations/PF-05/README.md` and frozen `docs/lean/statements/PF-05/ORIGINAL.md` have the same SHA-256, `f7acc0629067696f7aa2828673740e286730fb9654348b742752eb146a840f71`, at published base `47006df8b3a6c724a557266c891893d03e69323a`. The local `NLA/Statements/PF05.lean` and `Reviewed/PF05.lean` are byte-identical to the already reviewed shared statement modules; their SHA-256 hashes are respectively `3ac9a2fb395d96c3b61c6f2593144caac010da4bfafd2d96f86627aa7a75859d` and `df79daee68563e5bb6a6d85cf70246bf2154f12bcc5fe5a6a806e8009e558b7f`. I also read the prior independent specification and Lean-boundary reviews under `docs/lean/statements/PF-05/reviews/`.

The reviewed local `Challenge.lean` has SHA-256 `6ad5b632ae12132c8a932eb40b24c028c9fe608bf7bd0eca40e91daa46ba207f`; `Check.lean` has SHA-256 `da82602cf2fc9822931f9bbfea90340f6d173b3d4aa9120b6ee980217ea614f9`.

## Exact target

`NLA.PF05.target` is stated as `NLA.Statements.PF05.Target`. It quantifies over every real entrywise nonnegative matrix of ordinary rank three and PSD rank exactly two, and every size-two PSD factorization. The equivalence includes zeros and singular factors. The direction side requires symmetric directions, vanishing first-order trace derivatives, and a common interval of PSD straight-line perturbations; it only allows one common scalar for trivial directions. The uniqueness side quantifies over every other size-two PSD factorization and requires one invertible real `2 × 2` congruence for the entire factor family. The matrix inverse is guarded by `S.det ≠ 0`. These are the mathematical conditions in the original question, with no added positivity, genericity, or commuting hypothesis. There is no numerical target to compute.

`Check.lean` checks the live and frozen targets with `#assert_statement` and `#assert_trust kernel`, and asserts their definitional equality by `rfl`. The Comparator configuration selects only `NLA.PF05.target`. The `sorry` in `Challenge.lean` is the intentional challenge hole; it must be replaced by the complete proof before any claim of Lean verification.

## Limits

I reviewed source text and local hashes. I did not run a Lean build, Comparator, or LeanCert proof-target job. I did not audit a proof implementation, because none exists in this packet. Any change to the listed statement or Challenge bytes requires renewed review before proof implementation.
