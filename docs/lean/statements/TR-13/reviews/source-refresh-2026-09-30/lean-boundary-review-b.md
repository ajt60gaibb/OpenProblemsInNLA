# TR-13 Lean-boundary source-refresh review B

Reviewer: `/root/refresh_tr13_review_b`, OpenAI Codex AI agent (`is_ai: true`).
Date: 30 September 2026 (UTC). Verdict: **approve** for the bound inputs below.

This is an independent source-level re-review after implementation, prompted
by the canonical source refresh. I am distinct from author `/root` and did
not implement or edit the reviewed specification or Lean definitions. No
fresh Lean elaboration, axiom report or Linux Comparator execution is claimed.

## Exact boundary and imported meanings

I read the complete current canonical README, refreshed ORIGINAL.md and
specification, live and frozen TR13 modules, live and frozen TR14 modules,
the shared Infrastructure module, implementation correspondence notes and
all three package-pin files. The required local import closure calculated
by tools/lean_statements/check.py consists of live TR13, frozen TR13, shared
live TR14 and Infrastructure. Frozen TR13 deliberately imports live TR14;
that shared dependency is included and hash-bound. Frozen TR14 was also
inspected and bound as an additional input. Neither module imports the
separate TR-13 solution project advertised by the new canonical notice.

The live and frozen TR13 files match their historical metadata hashes and
are exact copies under the prescribed leading comment and namespace
substitution. The same direct source comparison succeeds for TR14. The
source refresh adds only the 30-line formalization notice, while the
specification changes only its provenance paragraph. The target itself
and all imported local mathematical definitions remain unchanged.

The actual Target is a closed Prop definition with universal m,n guards
5 <= m, Odd m and 2 <= n. It existentially chooses an MvPolynomial over all
m(n-1)+1 complex coefficients, witnesses a nonzero evaluation and then
requires EqualFiveRanks throughout its nonvanishing locus. Genuine
MvPolynomial evaluation supplies the principal-open condition; no arbitrary
rank or genericity predicate replaces mathematics. The principal-open
formulation is equivalent to existence of a nonempty affine Zariski open.

TR14.HankelIndex computes the full finite sum of zero-based indices with
a proved bound, and Hankel reads that coefficient. OrdinaryWidth is a
sum of arbitrary products of complex vector entries; SymmetricWidth is a
sum of complex-scaled pure powers. No conjugation, real-data constraint or
Hankel restriction is inserted in the decomposition factors.

VandermondeVector is a^(n-1-i)*b^i. On Fin n with n >= 2 the natural
subtraction does not truncate an intended negative exponent. The nonzero
pair disjunction allows a=0 or b=0 individually, including infinity; c may
vanish. OrdinaryBorderWidth uses arbitrary ambient tensor sequences with
ordinary width r. SymmetricBorderWidth constrains each tensor only by
symmetric width r. Both use every-coordinate Tendsto atTop to nhds in the
usual complex topology. Their sequences need not remain Hankel.

EqualFiveRanks explicitly contains all four equivalences with ordinary
width for every r, including zero. The empty sums and zero padding have
the intended meaning. All five threshold sets have finite minima for these
Hankel tensors, so equality of all thresholds is equality of the actual
five ranks. The target neither adds the known generic-rank formula as a
new subquestion nor drops any of the original equalities or quantifiers.

## Infrastructure, pins and limits

Infrastructure's #assert_statement requires a safe definition whose type
is exactly closed Prop, and examines its complete axiom closure, allowing
only propext, Classical.choice and Quot.sound. Both TR13 copies set
leancert.trust to kernel and invoke the statement and kernel-trust checks.
The pin files specify Lean 4.33.1, LeanCert
621a43d7cf21f87872392a01e874f2f1dbddc926 and Mathlib
0df444a360eaa60ab8c11dca51a86af692955474; every manifest dependency has a
concrete revision. These are unchanged inputs, not newly tested builds.

No blocker remains in the refreshed statement boundary or source binding.
This approval covers exact source-level correspondence and pinned imported
meaning; it does not assert Target, validate the separate solution project,
replace execution checks, or convert historical logs into a fresh pass.
The full 30-target Linux verification remains the coordinator's separate
gate. No catalog status or permanent ID is changed by this review.

## Reviewed input SHA-256 bindings

- `docs/lean/statements/TR-13/IMPLEMENTATION_NOTES.md`: `11300fbbcd0c6c4917d4a49a30de552ad71d155778673576cb63d345208a7d15`
- `docs/lean/statements/TR-13/NUMERICAL_TARGETS.md`: `8238e5adadcc23223017e7900a751f9cd0318b5375886b5543b4b8eb9303d91d`
- `docs/lean/statements/TR-13/ORIGINAL.md`: `fa34e46c5869e28c9f198a1aa78a4a5e026ba99dcbe67ce10d3410e426f7f70b`
- `docs/lean/statements/TR-13/reviews/source-refresh-2026-09-30/README.md`: `abd6d3efd86f6431f3e19590480dc141b0eefec9a5c51952aab4e97aedce8fdd`
- `docs/lean/statements/TR-13/reviews/source-refresh-2026-09-30/previous-original.md`: `da720e9599af7271686127b618b21038685e52a754031c2d43915c9d255f015f`
- `docs/lean/statements/TR-13/reviews/source-refresh-2026-09-30/previous-specification.md`: `1df6ae38c9f787c4d0994c676f149e0fc02ed94b85e5d6e0e65c7e236d744b3d`
- `docs/lean/statements/TR-13/reviews/source-refresh-2026-09-30/previous-statement.json`: `2db388f56748ad553da877334d097ecc01898f11e1523b3da857c03d5d0bdc7c`
- `lean-statements/NLA/Statements/Infrastructure.lean`: `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37`
- `lean-statements/NLA/Statements/TR13.lean`: `5b43b0a5410d91a7ec9a796a3e6d7cdd50f75929797d2eca4587cb2b0905a99d`
- `lean-statements/NLA/Statements/TR14.lean`: `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9`
- `lean-statements/Reviewed/TR13.lean`: `8b876a24f87eeecdb983ca6044b7548aa629db0a3f0fe9c3878516cba8b29b16`
- `lean-statements/Reviewed/TR14.lean`: `9990f933adf8a8593f6a1fcc70aeeaeed8abdfe05e7738bd5b538e719ad9c356`
- `lean-statements/lake-manifest.json`: `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8`
- `lean-statements/lakefile.toml`: `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40`
- `lean-statements/lean-toolchain`: `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`
- `tensor-computations/TR-13/README.md`: `fa34e46c5869e28c9f198a1aa78a4a5e026ba99dcbe67ce10d3410e426f7f70b`
