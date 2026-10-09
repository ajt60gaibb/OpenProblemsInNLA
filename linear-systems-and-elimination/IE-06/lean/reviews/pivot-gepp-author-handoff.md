# IE-06 nonsingular path-existence proof handoff

Date: 2026-10-06. Author: infrastructure agent, assigned a bounded deterministic
proof task after the user requested the full probabilistic proof. This is an
author handoff, not an independent review. The coordinator and independent
mathematical reviewer approved the exact interface before these files were
written.

The new theorem is

```lean
theorem admissiblePath_exists_proved {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) :
    ∃ path : PivotPath n, AdmissiblePath A path
```

It exactly supplies the semantic obligation in the unchanged Challenge. It
has no Gaussian, growth-bound, tie-uniqueness, or positive-dimension hypothesis.
Dimension zero uses the vacuous path. The original all-path exceedance event
is unchanged: the deterministic scan merely provides an existence witness.

## Source ownership and exact identities

| File | SHA-256 |
| --- | --- |
| `NLA/IE06/Pivot.lean` | `be17ad9e8ca2ddad1559968fe0ad91abf0b9ce127c17c5bdf665a14976455739` |
| `NLA/IE06/GEPP.lean` | `28c6de0c446c07d151d59bf8c3b8576255eac6163400ef8ba77dac0e2f6efd36` |

The implementation adapts the corresponding IE-04 files at repository commit
`286d8768fbd9a69264daa88e285680293db29837`, retaining George Stepaniants's
copyright, Caltech affiliation, Apache-2.0 license notice, AI-assistance
disclosure, and the original IE-05 provenance. Pivot's auxiliary scan
definitions are colocated in the new Pivot file. GEPP omits the unrelated
entry-maximum/growth-bound half of the older module and retains only the
supported-vector injectivity argument and its path consequences. The new
files depend only on the local IE-06 core and pinned dependencies, not an
IE-04 package import.

## Mathematical proof structure

The ascending scan retains the earlier row on equality. Its score assigns
inactive rows a negative value, whereas active absolute values are nonnegative.
The existing `List.argmax` argument proves active-row maximality and least-index
tie selection. A nonzero active column then makes the chosen maximum nonzero.
The recursively generated scan trajectory agrees with the existing trajectory
for the resulting path.

`ActiveInjective S k` means that a vector supported on indices at least k and
annihilated by all active rows of S is zero. A nonsingular input has this
property at stage zero. Permuting active rows preserves it. An active column
cannot vanish, since the corresponding unit vector would contradict this
injectivity.

To prove Schur preservation, extend a putative supported kernel vector by
choosing its pivot coordinate to cancel the pivot-row equation. The Schur
equations then show that the extended vector is in the preceding active
kernel. It is zero, so the original vector is zero. Induction supplies a valid
nonzero maximum-column pivot at every stage and hence the desired admissible
path. No claim is made about the determinant of the zero-padded full
intermediate matrix.

## Actual local verification

Both new files compiled on their first check. Every exported proof has an
explicit LeanCert `#assert_trust kernel` assertion and printed transitive
axioms. The final theorem and all other displayed GEPP proofs depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

The full local source-snapshot check passed at
`verification/local/attempt-5f94q422/result.json`, SHA-256
`c26fc82c3002d31e7ed66c85d4a8f5906415cdbc07e2e2a3d1ba19ca760eb02f`.
Its systematic audit checked all 93 then-current concrete local declarations,
and the sorry/native controls were rejected as intended. This evidence uses
the explicitly trusted pinned local dependency cache; it is not fresh Linux
sandbox/Comparator verification and does not prove the outstanding Gaussian
tail theorem. No frozen definition, Challenge signature, canonical problem
file, commit, or remote repository state was changed.
