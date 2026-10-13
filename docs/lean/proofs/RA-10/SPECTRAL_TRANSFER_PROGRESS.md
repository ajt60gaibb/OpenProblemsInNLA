# RA-10 spectral perturbation and ridge transfer

**Status (2026-10-11): full RA-10 is now locally proved with constant 11.**
This extends the existing RA-10 draft at
`50106db1b75a1019b708f495db747ab37bb8efbd` on branch
`codex/ra10-spectral-transfer`. The later `OperatorMonotoneRepresentation.lean`
proves `TransferBound 11` and the unchanged `Target` unconditionally.
The canonical problem, source solution, frozen statement, dependencies, and
catalogue status are unchanged.
The [completion checklist](COMPLETION_CHECKLIST.md) records the remaining
review and verification work. The subsequent
[representation progress note](REPRESENTATION_PROGRESS.md) records twenty-seven
more modules, including the general representing measure, Bendat–Sherman,
the harmonic extreme-point classification and the final target.

## New results

All modules are under `lean-statements/NLA/Proofs/RA10/`.

| Module | Exact scope |
| --- | --- |
| `HermitianPositivePartOrder` | For Hermitian `M`, both `M₊` and `M₊ − M` are positive semidefinite. |
| `OrderedSpectralNuclearPerturbation` | For any supplied ordered PSD decompositions, `∑ᵢ |λᵢ(X) − λᵢ(Y)| ≤ NuclearNorm (X − Y)`, with coefficient one. |
| `SelectedSpectralNuclear` | Exact nuclear norms of spectral matrices, differences of truncations in the same supplied basis, and optimal spectral tails; positive tail implies positive cutoff. |
| `SelectedApproximantPerturbation` | Source (16)–(18): `r ≤ e(B)`, `e₀ ≤ e(B) + r`, and the selected ridge perturbation estimate. |
| `RidgeTransferConditional` | The full constant-11 ridge conclusion, using the frozen nuclear norms on both sides, **assuming the source compression estimate**. Includes an unconditional zero-tail ridge lemma. |
| `RidgeCompressionMass` | Source (5) from the two block-energy equations, allowing singular compressed matrices. |
| `RidgeCompressionEnergy` | Derives those equations from actual ridge eigenvectors, with arbitrary orthogonal projections and possibly singular compression. |
| `RidgeCompressionQuadratic` | Bounds each positive ridge eigenvalue using quadratic forms of the two positive parts. |
| `PositivePartTraceBound` | Reusable positive-part trace bound by summing quadratic forms over a full orthonormal eigenbasis. |
| `RidgeCompression` | Proves the full source Lemma 2 for all positive shifts and cutoffs. |
| `RidgeTransfer` | Proves the constant-11 ridge transfer with no compression hypothesis, including zero tail. |

The eigenvalue perturbation proof uses the common PSD upper bound
`U = Y + (X − Y)₊`, ordered eigenvalue monotonicity, and the positive-part
trace identity. It does not assume commutation, invertibility, distinct
eigenvalues, or a gap at the cutoff.

The only edit to an existing proof module is a seven-line public wrapper
`nuclearNorm_diagonal` in `HermitianPositivePart.lean`, reusing its existing
private proof. Existing hash-specific reviews do not certify these new bytes.
No new modules have been added to the reviewed aggregate imports.

## Compression simplification

Write `qH = uᵀAu`, `qE = uᵀAw`, `qF = wᵀAw`, `U = uᵀu`, and `W = wᵀw`.
The source block equations imply

```text
qE = −μ(sU + qH),
qF = μs(U − W) + μ²qH.
```

Testing positive semidefiniteness at `μu + w` gives

```text
0 ≤ (μu + w)ᵀA(μu + w) = μs((1 − 2μ)U − W).
```

For `μ,s > 0`, this yields `W ≤ (1 − 2μ)U`. With `U + W = 1` and `μ < 1`,
it gives `U ≥ 1/(2(1 − μ))`. These implications are checked in
`RidgeCompressionMass.lean`; no inverse of the compression is used.
`RidgeCompressionEnergy.lean` now derives the equations from actual
eigenvectors by inverting only `sI + A` and `sI + C`, which are invertible
even when the original matrices are singular. Regularisation and limits are
therefore unnecessary in this implementation.

There is a second simplification. For each unit eigenvector `v` with positive
ridge eigenvalue `ℓ`, the checked bound is

```text
ℓ(s+c)/2 ≤ vᵀ[(C−A)₊ + (cP−C)₊]v.
```

The right-hand matrix is PSD. Nonpositive eigenvalues contribute zero and
satisfy the corresponding bound automatically. Summing over the full
orthonormal eigenbasis proves Lemma 2 without a separate variational maximum
over projections or a support theorem for the defect's positive part.
The non-strict bound `ℓ ≤ 1` suffices; strict resolvent positivity is also
unnecessary for this argument.

Reuse was checked against the current upstream draft (still the baseline
commit above), existing RA-10 modules, and the pinned Mathlib matrix APIs.
The original source solution is unchanged; these implementation
simplifications still require independent review.

## Checks and remaining work

Using the unchanged Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926` pins, these commands passed from
`lean-statements/`:

```bash
lake build NLA.Proofs.RA10.RidgeTransferConditional
lake build NLA.Proofs.RA10.RidgeCompressionMass
lake build NLA.Proofs.RA10.RidgeTransfer
```

The last builds all new spectral, compression and transfer modules transitively. Every
new exported result is covered directly or transitively by
`#assert_trust kernel`; printed axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. There are no admissions or custom axioms.
Successful build logs are retained in
`verification/2026-10-11-spectral-transfer/` beside this note.
The final ridge run is `ridge-complete-build.log` (2794 jobs);
`ridge-source-sha256.txt` records the RA-10 source and dependency-configuration
hashes checked by that run.

The later representation development completes the mathematical proof.
Independent reviews and the required isolated non-root Linux Comparator
checks remain outstanding. The local macOS builds are not that verification,
and the canonical status and reviewed aggregate remain unchanged.
