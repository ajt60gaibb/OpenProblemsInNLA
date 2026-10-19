# TR-14 fresh independent preproof statement approval 1

Date: 2026-10-18. Reviewer: OpenAI Codex AI agent `/root/solved_inventory`.
Decision: **APPROVE the unchanged exact statement for implementation.** This approves statement fidelity and the proposed proof scope, not a complete proof of TR-14. A second fresh independent statement approval is required before new proof bodies. No new proof bodies were written during this review.

## Inputs and immutable identity

The retained candidate is commit `fdb40b66425ec58e4806cee93d2aaf92a0f8597c` in `/Users/ajt253/.codex/worktrees/tr14-lean-proof/OpenProblemsInNLA`. That checkout was read only, and its working tree was clean before and after this audit. The registered ID remains **TR-14**, at **tensor-computations/TR-14/README.md**. No ID, path, original statement, canonical document, existing proof source, index, or other chat's worktree was changed.

| Input | SHA-256 |
| --- | --- |
| Canonical README and byte-identical ORIGINAL.md | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| Complete resolution source solution.tex | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| NUMERICAL_TARGETS.md | `6c50aa83745fc3d096e08b476fb08a841ffc0fefb2cdd58511f924c49f09da17` |
| Live NLA/Statements/TR14.lean | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Frozen Reviewed/TR14.lean | `9990f933adf8a8593f6a1fcc70aeeaeed8abdfe05e7738bd5b538e719ad9c356` |
| NLA/Statements/Infrastructure.lean | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |

`input-inventory.json` gives exact hashes and declarations for all 39 retained proof modules, dependency pins, the registry and the generated problem document. Exact input bytes are preserved under `sources/` here. Removing only the frozen file's initial boundary comment and changing its namespace to the live namespace makes live and frozen files byte-identical. Their different file hashes therefore do not hide mathematical differences.

## Exact meanings reviewed

The source asks equality of the least ordinary and symmetric exact decomposition lengths for **every** complex Hankel tensor of order `m ≥ 3` and mode dimension `n ≥ 2`. The live/frozen target quantifies over those same natural parameters, every `h : Fin (m*(n-1)+1) → ℂ`, and every natural width `r`, and asserts:

```
OrdinaryWidth (Hankel h) r ↔ SymmetricWidth (Hankel h) r
```

I reviewed all definitions rather than only that final line. `HankelIndex` sums the zero-based input indices and proves its finite bound. This is exactly the canonical source's one-based sum minus `m`. Every allowed moment index is attained, as the retained `MomentIndex` module proves. `Hankel` uses that actual coordinate, not a supplied semantic invariant.

`OrdinaryWidth` permits a separate arbitrary complex vector in every summand and every mode. `SymmetricWidth` permits a complex scalar and one vector repeated in every mode. Both identities are required at every coordinate tuple, with ordinary complex multiplication and no conjugation. There is no imposed normalization, Vandermonde shape, genericity, bound on `r`, or bound on the apolar algebra dimension relative to `n`. These are exact ranks, not border ranks.

The formulation with every width is faithful to equality of the minimum widths. Zero terms can pad both predicates, so a width witness is also a witness at any larger width; the retained `WidthPadding` module proves this explicitly. Symmetric-to-ordinary absorption puts each scalar in one chosen mode, which exists because `m ≥ 3`. Ordinary decompositions always exist by the finite coordinate expansion. Symmetric finite decompositions exist here, for example by evaluating at `D+1` distinct complex nodes and solving the moment Vandermonde system, where `D=m*(n-1)`. Hence the minimum witness sets are nonempty and their equality is equivalent to the all-width equivalence. The planned hard-direction proof may instead select the least ordinary width below a supplied witness; it need not introduce default numerical ranks or assume any witness oracle.

The width-zero predicates are empty sums and both mean the zero tensor. The target includes `h=0`, width `0`, width larger than the tensor rank, `m=3`, `n=2`, repeated-root and mixed-root exceptional data, and the balanced endpoint `D=2ρ-2`. None of these can be removed in implementation.

The stronger quantitative rank formula in the resolution is useful for proof organization but is not part of the frozen target. In particular, a proof need not export a new invariant called rank or identify every affine chart root count with the original projective count if it proves both upper bounds and the ordinary lower bound in one consistently chosen normalized chart and transports the resulting width witnesses back.

I also checked the originating [Nie–Ye Conjecture 6.3](https://arxiv.org/pdf/1706.03631). It asks the same unrestricted ordinary/symmetric Hankel rank equality. Earlier generic cases in that paper do not narrow this target.

## Source route and current limitations

I read the full relevant argument in solution.tex, Sections 1–5: finite moment algebra, both symmetric upper bounds, the transformation/contextual product inequalities, and the arbitrary ordinary-decomposition lower bound. The terminal-sequence appendix was also checked; its specialized family cannot replace the mixed-root lower bound. I found no statement-fidelity blocker. The source's contextual finiteness argument must actually be formalized: a general product-space inequality cannot simply be assumed in a nonreduced algebra.

The 39 modules stop short of the target. They establish normalization, finite moment/Frobenius structure, exact local Fourier symmetric upper witnesses, coordinate transports, padding, and now a top-remainder/representer-unit inverse. They do **not** establish the binary pencil upper bound or the unrestricted ordinary lower bound. There is no exported theorem of the frozen `Target`. `ROUTE_AND_GATES.md` records the exact remaining route, with endpoint obligations and a counterexample to treating the local upper bound alone as sufficient.

The original mathematical resolution remains attributed to Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation, as retained in the source. This is an AI preproof statement review, not external human peer review or a claim that the mathematical resolution has now been formally verified.

## Reproducible retained-source check

A fresh isolated source replay passed **42/42 commands**: all 39 retained proof modules, the shared Infrastructure file, live statement and frozen statement. It used Lean `4.33.1`, pinned Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. NLA objects were rebuilt from the private source snapshot into a newly created temporary output directory; only pinned dependency objects were reused. All recorded source hashes were unchanged during the run. Kernel trust assertions in those sources passed, and the printed theorem axiom lists contain only foundational axioms. This is local macOS evidence; it asserts neither full-target proof nor Linux/Comparator success.

Reproduce with an existing cache containing those exact pins:

```bash
python3 check_retained_sources.py \
  --dependency-root /private/tmp/nla-sp12-lean-oct18/lean-statements \
  --lean-bin /private/tmp/pf05-tooling/elan-home/toolchains/leanprover--lean4---v4.33.1/bin
```

Run from this report's directory. The cache path and Lean binary path are environment arguments; the source snapshot and hashes are retained here. `retained-build.json` records every command, source/log hash, elapsed time and outcome. A repeat creates fresh objects and refreshes that run receipt and logs without altering any checkout. The immutable input snapshot is independent of those refreshed run outputs.
