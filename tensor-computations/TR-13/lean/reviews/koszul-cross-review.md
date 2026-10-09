# Koszul proof component cross-review

Date: 2026-09-28.
Reviewer: OpenAI Codex agent `/root/environment` (AI agent).
Phase: implementation review of the Koszul lemmas and explicit shift witness.

## Scope and independence

I read and audited `NLA/TR13/Koszul.lean` and
`NLA/TR13/KoszulWitness.lean`, authored by a different agent. I did not edit or
implement either file. I did implement the supporting
`MatrixCertificate.lean` and the separate `LowerRank.lean`; neither is given
independent approval by this report. In particular, the imported
`matrix_rank_ge_sub_of_kernel_coordinates` is my own contribution. This is a
transparent component cross-review by a project contributor, not an
independent whole-project referee report, human peer review, or source-author
endorsement.

The mathematical source is the full manuscript
`references/colbrook-recovered-tensors-2026-09-11/manuscripts/TR-13.tex` at
repository revision `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`, SHA-256
`2adb85e04d4d257399049fea3f4e946f6a8d586349bbab411a372de9207f07ea`.
Its relevant arguments are the three-slice rank certificate and two-spike
generator sections. The retained canonical README has SHA-256
`da720e9599af7271686127b618b21038685e52a754031c2d43915c9d255f015f`.

## Reviewed file hashes

| File | SHA-256 |
| --- | --- |
| `NLA/TR13/Koszul.lean` | `4b5d51a9c32de19ba90507522e41567f7e1452c8983e435481b96310ddba87eb` |
| `NLA/TR13/KoszulWitness.lean` | `027d7f54fec3fbc88c1b5c0eb7ccd7932caf2c06d37044cb26f404063423b315` |

## Mathematical inspection

1. `koszul` has exactly the manuscript's nine blocks
   `[-M1,M0,0; -M2,0,M0; 0,-M2,M1]`. The index type
   `Fin 3 × Fin a` represents all `3a` rows and columns. Its definition is
   also polymorphic in the coefficient ring, allowing a genuine polynomial
   matrix to use the same block formula.

2. `scalarKoszul_rank_le` correctly handles both zero and nonzero slice
   coefficient vectors. In the nonzero case the column `c` is a nonzero
   kernel vector: multiplying the scalar Koszul matrix by `c` gives zero by
   exact commutative algebra. The matrix product rank inequality therefore
   bounds its rank by two. No division by a potentially zero coefficient is
   used.

3. `koszul_pure_rank_le` explicitly factors the Koszul matrix of entries
   `c[j] * u[x] * v[y]` as `L * scalarKoszul c * R`. The selector matrices
   `L` and `R` include every block coordinate. Rank monotonicity under matrix
   multiplication transfers the bound of two. The lemma covers zero vectors
   and zero coefficients, which is necessary for padded decompositions.
   `koszul_add`, `koszul_sum`, and `continuous_koszul` then provide the
   relevant exact algebra and ordinary topology interfaces.

4. `lowerShift` and `upperShift` use the intended zero-extended finite
   shifts. Their multiplication formulas branch exactly at the endpoints
   `d <= i` and `i+d < a`; the proof does not read out-of-range coordinates.
   The definitions `spikeB = lowerShift a s` and
   `spikeC = lowerShift a (2*s) + upperShift a (a-s)` match the reversed
   slice form in the manuscript.

5. `spike_comm_first` and `spike_comm_second` establish the two nonzero
   diagonal blocks of `C B - B C` on the first `2s` rows and last `2s`
   columns, with signs `+1` and `-1`. Proving only those rows is sufficient
   for the subsequent lower bound. The kernel equations in
   `koszul_identity_mulVec_zero/one/two` have consistent signs:
   `x1=B*x0`, `x2=C*x0`, and `C*B*x0-B*C*x0=0`.

6. `spike_koszul_kernel_determined` combines these equations correctly.
   The first `a-2s` coordinates of `x0` are supplied as zero, and the
   commutator forces all remaining coordinates to zero. Then both other
   blocks vanish. `spike_koszul_rank` applies the imported kernel-coordinate
   bound to obtain `3a-(a-2s)=2a+2s`. Its hypothesis `2s <= a` is sufficient;
   it does not silently require `s > 0`.

7. The important binary endpoint `s=0` is covered. The upper shift by `a`
   is zero, both normalized slices are the identity, and the Koszul kernel
   consists of triples with all three blocks equal. The bound is then
   `2a`. In the intended `n=2` application the second moment spike is at
   `2a-1=D` and is invisible to the repeated middle-coordinate-zero slices,
   whose moment indices are at most `2a-2`. Repeating that middle coordinate
   is a fixed linear map, so it preserves decomposable tensors; distinct
   selected middle coordinates are not needed. Connecting this observation
   to the actual Hankel witness is a separate obligation of `Lower.lean`.

## Reuse, correctness limits, and verdict

The files reuse Mathlib matrix rank, determinant, finite-sum, and rank-nullity
interfaces rather than redefine rank. Their specialized definitions are small
coordinate formulas suitable for the source argument. I found no `sorry`,
custom axiom, `native_decide`, or suppressed proof obligation in either file.
The compiler-noise cleanup changed only tactics, not definitions or theorem
types.

I independently ran `lake build NLA.TR13.KoszulWitness` in the pinned project
after the final cleanup and observed a clean successful build (3393 jobs).
I then ran `#print axioms` on `koszul_pure_rank_le` and `spike_koszul_rank`;
both reported exactly `propext`, `Classical.choice`, and `Quot.sound`, with
Lean exit code zero. These were local macOS development checks. No Linux
Comparator log was inspected for this component review.

**APPROVE the two reviewed components at these hashes.** No substantive
mathematical correction is requested. The fixed spike-to-Hankel identity,
ordinary ambient border-sequence bridge, upper-bound reconstruction, and final
generic theorem are outside this component verdict. A successful ordinary
Lean build is not the repository's fresh Linux Comparator verification.
