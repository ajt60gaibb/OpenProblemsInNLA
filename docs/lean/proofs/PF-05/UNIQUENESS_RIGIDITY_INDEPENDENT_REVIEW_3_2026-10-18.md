# PF-05 unrestricted uniqueness-to-rigidity implication — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026. I authored no PF-05 proof source and made no proof edits. **APPROVE the complete unrestricted reverse implication `unique_implies_infinitesimallyRigid M A B hfact hrank hunique`. This is one direction of the frozen equivalence, not a full PF-05 Target proof.**

The already-reviewed G01 source remains exact. The additional frozen sources reviewed completely here are:

| Module | SHA-256 |
| --- | --- |
| CoordinateActions | `63c36197a129f745ce0843b013e149697b157c6ab0d7aa0567ced4a862f9d363` |
| InfinitesimalActions | `f8ddcd810c1556ffce9f8e4c7c85e90e2792d5cf2e08b5dc37d709b6b406cd59` |
| Resolvent | `51c23f8fd62a78ab0d504b67bcfb9d36dedd8dadafd179b5ed9510a0b7ce022d` |
| PSDLine | `7b688bdd5986be23c414faac6fcd4a494242caf2f354972c38ba1e3513139fc6` |
| OneSidedPSD | `497369e6cc7f0bfb8aa0e8d97796ab98cb7b7224f4f24cc6846d39cd0381d43d` |
| PSDResolvent | `13aea085658ece42de088f58e767ca20671b035750ba52fac972c03242f93a3b` |
| OperatorFactorization | `e0f86b9b36f5f50b1a478323886d33103ddb16138c751a40598e6286028fc626` |
| FeasibleIntegration | `4ebd08d96ed0292c94bf6530a5bfa6b54d8628419bf4e5b95465c855044f187f` |
| CongruenceLine | `795a11708b88c3875cf34f8de1a516a92c34e54d505318636012f7f940e8cc30` |
| UniquenessRigidity | `17755de16b3774dd857a51e04133ad8098e5f8501da8cf9368e03e5212b0d048` |

The hypotheses of the final implication are exactly an actual real size-two PSD factorization, ordinary rank three, and the frozen `UniqueUpToCongruence` property. Its conclusion is the frozen straight-line `InfinitesimallyRigid` predicate. There is no positive-entry, nonzero-row/column, distinct-ray, strictly-positive-factor or local-orbit premise. Other full Target domain assumptions are unnecessary for this stronger individual implication.

The coordinate actions use primal rows `(A00,A11,A01)` and dual columns `(B00,B11,2*B01)`, with inverse decoding dividing the third dual coordinate by two. Decoding/injectivity and the actual first-order operator identify every supplied direction as E=primal(T,A) and F=−dual(T,B). The primal and dual operators act on the **three-dimensional coordinate space**; they are not asserted to be size-two congruences or to preserve the whole PSD cone.

`Resolvent` defines the actual inverse pencil `(I+tT)⁻¹`. Standard inverse differentiation at the identity gives derivative −T, and continuous entry evaluations give the actual scalar derivatives of every inverse-dual matrix entry. The module uses genuine matrix operator-norm structures for this internal calculus; its conclusions about scalar entry functions and real intervals use the ordinary real topology. The five named local norm/algebra/topology instance definitions are constructed from Mathlib's matrix operator-norm structures and receive the additional direct checks described below. They are not added assumptions. Continuity of the actual pencil determinant, whose value at zero is one, proves a genuine nonsingular interval.

The PSD boundary argument is exact. The determinant of a straight line through a symmetric two-by-two matrix is `det(B)+t*determinantDirection(B,F)+t²*det(F)`. Actual one-sided PSD feasibility through a singular factor forces the linear coefficient nonnegative. If that coefficient is zero, feasibility also forces det(F) nonnegative. For a **nonzero rank-one** B, explicit two-coordinate identities then force F to be scalar B, using either positive diagonal of B. This includes flat boundary directions and does not treat a generic second-order error as automatically feasible.

For the actual inverse-dual path, all possibilities are handled. A zero B remains exactly zero by linearity. A positive determinant stays positive locally together with the positive trace. At a nonzero singular B with strictly positive determinant derivative, scalar derivative calculus gives a positive determinant for all sufficiently small positive times, and trace positivity persists; symmetry, trace and determinant give PSD. In the remaining flat rank-one case, the preceding proportionality result makes B an actual eigenvector of the dual T. The guarded exact resolvent eigenvector identity then writes the inverse-dual path as a positive scalar multiple of B on a common neighborhood. The result therefore covers zero, positive definite, strictly outward and flat factors without omitting a boundary case.

`FeasibleIntegration` takes the original common feasible interval, the proved inverse-dual PSD interval for every column, and the determinant interval. Finiteness supplies one common column interval, including an empty indexing type without a new nonemptiness hypothesis. Intersecting those intervals gives h>0. The actual primal path is **exactly** A+tE. The dual path is the actual inverse-coordinate action and has derivative F by the proved entry identities. The nonsingular pencil times its actual inverse equals I, so the weighted trace-pairing identity proves **exact Factorization M** at every `0≤t<h`. No positive-time exact factorization of both original straight lines is assumed; the inverse dual path is constructed to give the needed exact products.

Uniqueness now applies to each of these actual nearby factorizations. The actual rank-three row span identifies its entire coordinate operator I+tT with the explicit coordinate operator of the resulting shared size-two congruence. This extension from the actual spanning factor family to all symmetric matrices is proved by a retained left inverse; it is not an assumed global cone-preserving property.

`CongruenceLine` then proves T scalar without choosing a differentiable family of congruence matrices. For any nonzero rank-one PSD X, the actual affine image X+t*primal(T,X) is both PSD and singular throughout the interval, since it is an actual congruence image. Evaluating the determinant quadratic at h/2 and h/4 proves its linear coefficient zero. The exact flat-segment lemma therefore makes every such X an eigenvector of the primal T. Four explicit rank-one PSD rays, namely the two diagonal units and the outer products of `(1,1)` and `(1,-1)`, force all those eigenvalues equal and every off-scalar entry of T to vanish. Thus T=dI. The weighted primal and dual scalar identities finally give the **same** d on all rows and −d on all columns, exactly as the frozen rigidity predicate requires.

The first immutable G02-only audit passed 16 Lean commands over 15 actual sources, checking 163 declarations and 136 theorem/lemma kinds. The subsequently completed unrestricted reverse closure passed **19 Lean commands**: all **18 actual sources** (16 proof modules and two statement/infrastructure modules) plus a separate consumer. It checks **184 explicit proof declarations**, with **154 theorem/lemma-kind checks** and nine directly located private constants (eight theorems and one definition). Every constant passes LeanCert kernel trust, and every printed transitive axiom closure is contained in `[propext, Classical.choice, Quot.sound]`.

Five explicitly named `local instance` definitions in Resolvent were covered transitively by that consumer. To make direct declaration coverage explicit, a **supplemental fresh audit** additionally checks those actual definition constants by unique environment name and kind. It passes eight Lean commands over seven actual sources, checking 86 declarations. A retained identity report verifies all seven supplementary source hashes equal the corresponding full reverse snapshots. The combined direct declaration coverage is therefore **189 distinct proof constants**, including all five named local instances. The source is unchanged; this is expanded audit coverage, not a proof repair.

Every local object in both audits is rebuilt from frozen snapshots into fresh isolated outputs excluding campaign project objects; only pinned dependency/core objects are reused. All source bytes and ten dependency revisions/tracked trees pass before/after checks. **All seven retained candidate modules** match their original retained lock both before and after, including retained modules outside these particular import closures.

```bash
python3 docs/lean/proofs/PF-05/verification/check-uniqueness-rigidity.py \
  --top UniquenessRigidity --evidence-name uniqueness-rigidity-review-3
python3 docs/lean/proofs/PF-05/verification/check-resolvent-instances.py \
  --top Resolvent --evidence-name resolvent-instances-review-3
```

Exact sources, consumers/drivers, hashes and raw logs are retained in [verification/feasible-integration-review-3/](verification/feasible-integration-review-3/), [verification/uniqueness-rigidity-review-3/](verification/uniqueness-rigidity-review-3/) and [verification/resolvent-instances-review-3/](verification/resolvent-instances-review-3/). All results explicitly record `full_pf05_target_proved: false` and `authoritative_linux_comparator: false`. The full forward-case assembly and full Target remain separate obligations. No proof, original page, target, permanent ID or canonical path was changed. This is independent AI-agent source review and local kernel evidence, not external human review or actual Linux/Comparator acceptance.
