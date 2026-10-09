# Scoped cross-review of the TR-13 lower assembly and final theorem

Reviewer: OpenAI Codex AI agent `/root/choose_algebra`.
Date: 28 September 2026.

**Verdict: PASS for the reviewed assembly and mathematical statement match.**
The reviewer did not author `Lower.lean`, `LowerRank.lean`,
`RankComparison.lean`, `Solution.lean`, `README.md`, or `formalization.yaml`.
The reviewer read the first four files in full, the exact frozen comparison
boundary, and both metadata files. The reviewer previously reviewed the
upper-bound modules separately in `upper-1.md`.

**Scope exclusion:** this reviewer authored `Koszul.lean` and
`KoszulWitness.lean`. This report does not independently certify those files,
and does not constitute a fully independent review of the entire dependency
closure. It is an AI-agent review, not human review or endorsement. No Linux
Comparator run was performed for this report.

## Inspected source hashes

| File | SHA-256 |
| --- | --- |
| `NLA/TR13/Definitions.lean` | `f026f45877d8e2bfc94a96c8be0dece8a1f2a843d8c1b7249891d720c42240c7` |
| `Challenge.lean` | `03d4522916e4763daf0c06a01393a31372c4eed4a0be48885eae6085598d4c8c` |
| `NLA/TR13/Lower.lean` | `55a8d56cb1c5afed1894da71e92eb77a0fc002825fe97d32563489e285733b76` |
| `NLA/TR13/LowerRank.lean` | `bf7afd3d2b04ea9daf42aa54260f1ba8f0f1e7da49e091d0c4b4e07582410602` |
| `NLA/TR13/RankComparison.lean` | `555d6e6ee61f29a4ddc3c199a1ee9ab71ea6a132961f92d2ce352a9817fdd6e3` |
| `Solution.lean` | `cca409d68bd917f58e8d97eaeded957ea4f4e3337b68a315b5d23b1cba32905e` |
| `README.md` | `e7c1101d889db48877bd0f781972be5f115504caf5a9a0ce9a69a5f9520aa456` |
| `formalization.yaml` | `5bf29cb9b0d13aaeb860ca3223c47e812bbd6a49ce84900573bada892b8ec1ba` |

## Lower-bound assembly

For `m=2k+1`, writing `ell=n-1`, `a=k*ell+1`, and `s=ell/2`, the
two-spike sequence is a genuine finite moment vector. Its distinguished indices
are `a-1` and `2*a+s-1`. The latter is at most
`D=(2*k+1)*ell`, because `s+1<=ell` for `ell>=1`; the former is plainly in
range. They are distinct because `a>0`. The code defines the vector directly
on the finite input index type and proves its normalized slice identities
entrywise, so it cannot accidentally use an unavailable moment coordinate.

The strict inequality `2*s<a` follows from `k>=1` and `2*s<=ell`. The three
normalized slices are exactly identity, the lower shift by `s`, and the sum of
the lower shift by `2*s` and the upper shift by `a-s`. The case split in
`twoSpike_normalized_slice` checks that the two possible contributions never
overlap. In the binary case `s=0`, selecting the same middle coordinate three
times is a valid linear map, and all normalized slices are identity. The
construction and the imported witness bound allow this case without a
positivity assumption on `s`.

`expectedRank_odd` correctly rewrites
`floor(((2*k+1)*(n-1)+2)/2)` as `a+s`. The oddness witness is converted to
`m=2*k+1`, and the original hypothesis `m>=5` implies the `k>=1` needed by
the witness theorem. No admissible order or dimension is omitted.

`LowerRank.lean` defines the compressed Koszul matrix on arbitrary tensors.
Every unrestricted ordinary decomposition gives its rank bound by linearity
and the pure-tensor estimate. The ordinary-border argument applies continuity
to the exact arbitrary sequence from `OrdinaryBorderRankAtMost`; it imposes no
Hankel, symmetric, bounded-factor, or fixed-decomposition requirement. Its
polynomial matrix is the actual specialization of this map on Hankel moments.
A high-rank witness therefore yields a nonzero determinant polynomial; this
genericity condition is constructed from the proved witness, not assumed.

## Final theorem and least-rank semantics

The final theorem multiplies the nonzero upper and lower polynomials.
The polynomial ring over the complex numbers is a domain, so that product
is nonzero. `principalOpen_nonempty` uses the polynomial function-extensionality
theorem over the infinite field of complex numbers to produce a point where
the product is nonzero. Hence the intersection is proved nonempty; the final
claim is not a vacuous universal statement over an empty open set.

At each point in that set, the actual Vandermonde decomposition supplies a
member of all five rank-defining sets. Symmetric coefficients are absorbed
into one mode for ordinary rank, using the true hypothesis `m>0`. Constant
sequences give the two border upper bounds, and symmetric-border sequences
also qualify as ordinary-border sequences. `least_eq` explicitly uses an
inhabited defining set in `le_csInf`, preventing an empty-set `sInf` artifact.
The universal ordinary-border obstruction then bounds every member of every
rank-defining set. All five exact equalities follow.

The declaration signatures in `Challenge.lean` and `Solution.lean`, from
`theorem generic_rank_equality` through the text preceding `:= by`, were
compared and are byte-identical. The frozen definition hash is unchanged.

## Independent local check

Ran successfully with the pinned local toolchain:

```text
lake env lean reviews/assembly-cross-check.lean
```

The script imports `Solution`, checks a literal copy of the complete target
type, and prints axioms for the final theorem, lower theorem, and rank-comparison
theorem. Each depends only on `propext`, `Classical.choice`, and `Quot.sound`;
see `assembly-cross-check.log`. The four reviewed proof source files contain no
`sorry`, custom `axiom`, `native_decide`, `unsafe`, or import of `Challenge`.

## Metadata review

The inspected README and manifest explicitly state that authoritative Linux
Comparator verification and full independent final review remain pending.
They identify the local compiler as macOS, accurately distinguish component
reviews from full independent review, leave `whole_problem_verified: false`,
and claim no human or source-author endorsement. The advertised full mathematical
scope agrees with the compiled theorem. This report does not independently
certify the repository workflow or manifest schema.

One packaging issue was reported to the coordinating agent: at the time of
inspection, the README's links to `reviews/README.md` and
`verification/README.md` pointed to files not yet present in the temporary
project. Those documentation files must be supplied before contribution. This
does not affect the proof verdict; their eventual contents are outside the
hashes and scope of this report.
