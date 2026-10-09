# TR-13 independent review of the existing local proof statement

**Reviewer:** `/root/proof_inventory` (AI agent), 9 October 2026.
**Verdict:** APPROVE the scope of the *local theorem statement* as covering the
complete canonical TR-13 target. This is a source-level mathematical boundary
review. It does not independently verify the proof body, rerun Lean, certify the
transitive axiom report, or substitute for isolated Linux Comparator/kernel
verification.

The canonical question quantifies over every odd order `m ≥ 5` and dimension
`n ≥ 2`, and asks for one nonempty Zariski-open subset of complex Hankel tensors
where ordinary, symmetric, ordinary border, symmetric border, and Vandermonde
ranks coincide. The local `NLA.TR13.generic_rank_equality` has those universal
format quantifiers, constructs a polynomial `p` with `p ≠ 0`, separately proves
`(principalOpen p).Nonempty`, and proves `AllRanksEqual (hankel h)
(expectedRank m n)` for every `h` in that open. The exact value is stronger than
the original equality-only target: `expectedRank m n = (m*(n-1)+2)/2` in natural
number division, or `ceil((m*(n-1)+1)/2)`.

`Definitions.lean` represents a tensor as its entire complex coordinate array
on `Fin m → Fin n`. Its Hankel index is the sum of zero-based indices, precisely
the source's one-based sum minus `m`. Ordinary summands are unrestricted
factorwise pure products. Symmetric summands allow independent complex scalar
coefficients. Vandermonde vectors are the homogeneous coordinates
`a^(n-1-i) * b^i` with `(a,b) ≠ (0,0)`, including the projective endpoint at
infinity. Empty and zero-coefficient sums are allowed.

Both border-rank predicates use actual sequences converging in the finite
coordinate product topology. Ordinary approximants are arbitrary ambient
tensors; symmetric approximants have symmetric decompositions but need not be
Hankel. Thus the ordinary border rank is not silently restricted to Hankel or
symmetric perturbations. The five ranks are infima of their finite-width
witness sets. `RankComparison.lean` obtains an actual Vandermonde width witness
on the advertised open and transfers it to the other four sets; its lower
bound for every ordinary border witness establishes the common minimum. This
prevents an empty-set `sInf` convention from manufacturing the claimed value.

`Solution.lean` imports `Upper`, `Lower`, and `RankComparison`, not
`Challenge.lean`. The latter is a separate comparison fixture with an
intentional placeholder. I found **no scope gap in the exported theorem
statement**. The principal open is expressed in the moment parameter space;
the original source itself parametrizes Hankel tensors by those moments, and
for `m ≥ 5`, `n ≥ 2` every index from `0` through `m(n-1)` occurs in an entry.
An explicit Lean equivalence of that parameter space with the Hankel subspace
is not part of this theorem, so it should not be claimed as a separately proved
bridge.

## SHA-256 of inputs reviewed

| Repository-relative path | SHA-256 |
| --- | --- |
| `tensor-computations/TR-13/README.md` | `fa34e46c5869e28c9f198a1aa78a4a5e026ba99dcbe67ce10d3410e426f7f70b` |
| `tensor-computations/TR-13/lean/NUMERICAL_TARGETS.md` | `5e9582f8125ad61ac473312dba9332bdeca5339a9b897570fdd20942deace5ca` |
| `tensor-computations/TR-13/lean/Challenge.lean` | `03d4522916e4763daf0c06a01393a31372c4eed4a0be48885eae6085598d4c8c` |
| `tensor-computations/TR-13/lean/NLA/TR13/Definitions.lean` | `f026f45877d8e2bfc94a96c8be0dece8a1f2a843d8c1b7249891d720c42240c7` |
| `tensor-computations/TR-13/lean/NLA/TR13/RankComparison.lean` | `555d6e6ee61f29a4ddc3c199a1ee9ab71ea6a132961f92d2ce352a9817fdd6e3` |
| `tensor-computations/TR-13/lean/NLA/TR13/Upper.lean` | `f02165febe8d37e531ba767e2bfdc3bd8467c68a39556e4e55b67bcb8867e8d9` |
| `tensor-computations/TR-13/lean/NLA/TR13/Lower.lean` | `55a8d56cb1c5afed1894da71e92eb77a0fc002825fe97d32563489e285733b76` |
| `tensor-computations/TR-13/lean/Solution.lean` | `cca409d68bd917f58e8d97eaeded957ea4f4e3337b68a315b5d23b1cba32905e` |
| `tensor-computations/TR-13/lean/Check.lean` | `86bfbfa5b7ad390fc960f410fdd787f411c653692203129a34a1375bda54b1c4` |
| `tensor-computations/TR-13/lean/comparator.json` | `cf41c450ca61d8d2969c387580905dd07b47c8ba527a06913309d80e6b1e3dbe` |

The hashes bind this review to the inspected files. They do not prove the
chronological order of earlier reviews or validate a historical build log.
