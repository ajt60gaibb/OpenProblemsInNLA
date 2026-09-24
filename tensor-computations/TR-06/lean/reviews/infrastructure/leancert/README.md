# Pinned LeanCert trust API preparation

AI agent `/root/tr06_infrastructure_audit`, 2026-09-24. Development infrastructure only. No numerical certificate, new mathematical theorem, TR-06 proof, Linux sandbox check or Comparator verification was run.

Pinned source: `/private/tmp/tr06-leancert`, git HEAD `621a43d7cf21f87872392a01e874f2f1dbddc926`, fetched from `https://github.com/alerad/leancert.git`. Tracked sources remain unchanged; `source-hashes.json` records their SHA256 hashes. `results.json` records actual commands, exits, logs, compiler and library paths. The actual Lean binary is the existing Lean 4.33.1 arm64 macOS installation in `/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.tools/lean-4.33.1-darwin_aarch64/bin/lean`.

At this revision there is **no `LeanCert.Tactic.Trust` module**. The actual module is **`LeanCert.Tactic.Verification`**, which imports only Lean core modules (`Lean`, `Lean.Meta.Native`, `Lean.Meta.Tactic.AuxLemma`). Compiling that one source module requires no Mathlib compilation, Lake dependency materialization, package symlink, or full LeanCert build:

```sh
cd /private/tmp/tr06-leancert
mkdir -p .lake/build/lib/lean/LeanCert/Tactic
/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.tools/lean-4.33.1-darwin_aarch64/bin/lean \
  -o .lake/build/lib/lean/LeanCert/Tactic/Verification.olean \
  LeanCert/Tactic/Verification.lean
```

For downstream development imports, prepend `/private/tmp/tr06-leancert/.lake/build/lib/lean` to `LEAN_PATH`; append the existing dependency `.../.lake/build/lib/lean` directories if also importing Mathlib. The retained script constructs these paths without writing to the shared package cache. A final reproducible project must retain the exact Git dependency and committed manifest rather than rely on these temporary development paths.

`recheck_trust_api.py` is an executable reproduction via `/private/tmp/tr06-python/bin/python`. It builds the trust module and runs `TrustAPIProbe.lean`; both exit 0. The probe sets `leancert.trust` to `kernel`, prints precise API signatures, and executes `#assert_trust kernel integrableOn_rpow_mul_exp_neg_mul_sq` on the already-existing Mathlib analytic theorem. Its printed axiom closure is exactly `propext`, `Classical.choice`, `Quot.sound`. No fake numerical certificate is added. This assertion checks an existing theorem's dependencies; it does not mean its proof was constructed by LeanCert.

Precise source semantics in `LeanCert/Tactic/Verification.lean`:

- Lines 51–57 register `leancert.trust`; default is `"native"`. Explicitly use `set_option leancert.trust "kernel"` in any certificate source. Individual tactics that accept the override can additionally use `(trust := kernel)`.
- Lines 324–350 implement kernel closure: construct a `mkDecideProof`, reduce the decision, reject false, and retain an auxiliary lemma through `mkAuxLemma` with `Elab.async=false` for eager kernel checking.
- Lines 471–521 dispatch `closeCertificateGoalTyped`: explicit `.kernel` selects only that kernel route and returns a hard failure if it cannot close. `.auto` is a separate branch which may fall back to native; do not substitute `.auto` for the requested kernel-only mode.
- Lines 593–663 implement `#assert_trust`. `classifyAxiom` permits `propext`, `Classical.choice`, `Quot.sound` as foundational; identifies compiler/native axioms including per-declaration native_decide auxiliaries; rejects `sorryAx` and unknown custom axioms. `#assert_trust kernel theoremName` checks the theorem's transitive axiom closure for absence of native/custom/sorry dependencies.
- The trust module provides the common verification boundary and trust assertions. It does not by itself import the full `leancert` numerical tactic router. Actual numerical tactic implementation lives in `LeanCert.Tactic.LeanCert` (and its dependencies), which was inspected but not built here.

The retained macOS development probe is separate from the repository's fresh non-root Linux Comparator/default-kernel acceptance gate. No claim of complete-target verification follows from this preparation.
