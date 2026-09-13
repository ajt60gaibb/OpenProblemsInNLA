# MI-23 — independent final proof referee 1

**Verdict: APPROVE for the complete local formal proof, at the hashes below.**
No mathematical correction is requested. Actual Linux sandbox execution,
Comparator matching and exported default-kernel replay remain separate pending
gates. This report alone does not authorize a `Lean verified` status.

Reviewer: `/root/solved_statement_inventory`, an independent AI agent, 12 September
2026. The implementation author is `/root/formal_review_standards`. I did not
write or edit this project's mathematical implementation. I completed the
mathematical review without reading final referee 2's report or conclusions.
The checks here were actually rerun by this reviewer; author-reported build
success was not used as a substitute.

## Source and frozen boundary

I read the complete canonical MI-23 README, complete Colbrook `solution.tex`,
submission `solution.md`, all definitions, all eight Challenge statements,
`NUMERICAL_TARGETS.md`, and all seven `NLA/MI23` source modules plus `Solution.lean`.
The PDF was checked for byte identity with its source revision, not rendered or
used as an independently inspected mathematical source.

The canonical files match immutable repository base
`8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`. Their SHA-256 values are:

| File | SHA-256 |
| --- | --- |
| Canonical `README.md` | `9edc47646606cc1a4317777b4556652038bf5f8ccdd96b9917ab902767c35fb5` |
| `solution.tex` | `a8eb6660e05afbafa9e376d1354d24f97cc0c25debd022e540e11859628b9552` |
| `solution.md` | `b05bd263ae7f3b2925c157e32ec5d3ec82bf62c3e5e7217144fca1029faa79c1` |
| `solution.pdf` | `2fab76272b1b340528631f26647a96c2105f615443246c33099e567ae534b5c2` |

The reviewed [proof freeze](proof-freeze.json) has SHA-256
`18fbf9a74e6006ca2b4159be62730c6df4faf38d472250b8ca1e7e54bf392ecb`.
Every one of its **25 files** matched before and after my checks. In particular:

| Project file | SHA-256 |
| --- | --- |
| `NLA/MI23/Definitions.lean` | `1ca2386528fc7ff944f84088842f62c5f33a38f14cde7ee8127972be29696def` |
| `Challenge.lean` | `283bca1ced50d7953f9946629c24e99f944d81095f9c822fbb3b58a44e01e189` |
| `NUMERICAL_TARGETS.md` | `2f8e41d440d3e24732a1c2b70c0710ad0d88367c2aac7979141959a8d8df25ee` |
| `NLA/MI23/FunctionalCalculus.lean` | `5603fb214d01f327ba297af151e278ed8f8310368272c59180dd52ebd87839a1` |
| `NLA/MI23/SpectralNorm.lean` | `af43452f42fde8c361d3ab21c4bcf9839f355b7c06f905dbc56c1eb591c6c5a3` |
| `NLA/MI23/NormBounds.lean` | `1fd4f9d91818470bfee7e3bb164baaaf120b80ee088ff827134be0e2ac867ad3` |
| `NLA/MI23/Witness.lean` | `4d7d79b742e614712d5ecc052c04df135cde6b6548ec7cb19f6cfbae0ef987b7` |
| `NLA/MI23/Arithmetic.lean` | `d5895f0636fa3aa3887721c610ee9f526cc35a6838e1d4ad7e7ba7f0548af3d9` |
| `NLA/MI23/Proof.lean` | `a82ba18b834453491e4d7bb50de23c08555b92bb70e573551d11e714a404984a` |
| `Solution.lean` | `575f2fd27922d2725d93ada823bfeb4da70407d7fd9c31fb7cf1753a5fdbd243` |

The recorded implementation gate binds both earlier statement approvals and the
three unchanged statement files. The only differences from the earlier
17-file statement freeze are the documented README progress text and the
`lakefile.toml` default target changing from `Challenge` to `Solution`; dependency
pins and mathematical statements are unchanged. All eight Solution theorem
headers match Challenge **literally**, with no whitespace normalization, and
match the exact Comparator selection. `definition_names` is empty.

## Mathematical fidelity and proof

The final negation retains every original quantifier: every `n ≥ 1`, all complex
positive-definite `A,B`, all real `r,s,p,t`, `p ≥ 1`, `0 ≤ t ≤ 1`, and both regions
`r,s ≥ 1` or `r,s ≤ 0`. Generalized means use the stated noncommuting factor
order and actual `CFC.rpow`; natural powers in certificates are ordinary matrix
products. No commutativity, rationality, diagonalizability certificate, or norm
comparison is added as an assumption of the conjecture or counterexample.

`orderedEigenvalues` starts from the complete characteristic-polynomial root
multiset. Its use of real parts is justified on the target domain: the generic
product theorem proves an invertible similarity to `Y^(1/2) X Y^(1/2)`, proves
the characteristic-polynomial equality, and supplies full reality, strict
positivity, descending order, dimension and determinant-product identities.
The equality back to the original complex-root multiset prevents losing
imaginary components or algebraic multiplicities. These are proved conclusions,
not assumed fields. Repeated eigenvalues are retained. Empty-list defaults in
`largestEigenvalue` cannot affect the target because the proved list length and
`n ≥ 1` exclude them.

`LogMajorized` contains every proper nonempty prefix-product inequality and
equality of the full products. The proof does not replace it by a largest-root
predicate. It proves failure of its first necessary prefix inequality for an
admissible three-dimensional pair, then specializes the entire universal
conjecture to that pair.

The generic norm bridge deserves particular attention. `operatorNorm` is the
norm of `Matrix.toEuclideanCLM`, not the default entrywise matrix norm. The
pinned `Matrix.Norms.L2Operator` instance is checked explicitly. Hermitian
unitary diagonalization and the genuine diagonal operator-norm formula identify
the norm with the largest positive root. Cyclic characteristic-polynomial
equality then identifies the first root of `X²Y²` with that of
`Y X² Y = (XY)ᴴ(XY)`; the C-star Gram identity gives `‖XY‖₂²`. The entry lower
bound is proved by applying the Euclidean linear map to a standard unit vector.
The upper bound is derived from the positive-semidefinite Gram matrix, its trace,
and the complete Frobenius sum. Thus the eventual scalar separation is connected
to the actual ordered spectrum by proved analytic statements.

The witness is exactly `D = diag(16,1/12,1)`,
`T = [[2,1,2],[1,25,-10],[2,-10,10]]`, `A=D²`, and `B=DT⁸D`.
The displayed LDL factorization, positive pivots, and invertibility of the
triangular factor prove actual positive definiteness. CFC identities prove
`A^(1/2)=D`, `A^(-1/2)=D⁻¹`, the normalized inner matrix `T⁸`, and its genuine
positive eighth and seven-eighth powers `T` and `T⁷`. Hence the means are the
actual `G=DTD` and `H=DT⁷D` for `r=s=1`, `p=2`, `t=1/8`.

My separate Fraction implementation recomputes powers by naive successive
multiplication, independently of the Lean addition-chain organization. It
reconstructs all seven displayed power/witness matrix certificates, the LDL
identity, positive principal-minor diagnostics for all six PD matrices, the
normalizing identity, every entry of `AB` and `GH`, and the full Frobenius sum.
It obtains exactly

```
(GH)[0,2] = 1260589125202 / 9
‖AB‖F² = 2009446159144992718181231562721 / 107495424
|(GH)[0,2]|² − ‖AB‖F² = 99434824489435745411095588895 / 107495424 > 0.
```

This supplementary calculation uses no numerical eigenvalue solver and is not
a substitute for the Lean proof. The Lean proof itself checks the matrix
identities and uses the strictly positive exact gap to prove
`‖AB‖₂² < ‖GH‖₂²`, the reversed first eigenvalue inequality, failure of complete
log-majorization, and finally the full conjecture's negation.

## Actual trust and independent execution

I independently re-elaborated Definitions, FunctionalCalculus, SpectralNorm,
NormBounds, Witness, Arithmetic, Proof and Solution in dependency order into a
new isolated prefix, excluding the author's project object directory from
`LEAN_PATH`. I then separately compiled Challenge and my own proof-term
inspector. All ten commands exited zero. Implementation and inspection emitted
no warnings; Challenge emitted exactly its eight deliberate placeholder
warnings. Challenge is not imported by the implementation.

The actual environment is local macOS arm64 with Lean **4.33.1**. All ten
dependency checkouts match their manifest revisions and are clean, including
untracked files. LeanCert is pinned at
`621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib at
`0df444a360eaa60ab8c11dca51a86af692955474`. The manifest SHA-256 is
`10e87dfa3fc8ecfaf18277f1a0838a3a009979e43555fe97474618ac9af250ff`.
Existing pinned dependency object caches were reused; I did not rebuild all of
Mathlib or run Linux Comparator during this review.

All **64 distinct implementation/public axiom reports** contain exactly
`propext`, `Classical.choice`, and `Quot.sound`, and their kernel trust assertions
passed. My inspector repeats the eight public trust/axiom checks. No custom
axiom, `sorryAx`, native-execution trust or unchecked reduction appears in these
transitive dependencies.

The independent inspector traverses **172 reachable project declarations**,
including private arithmetic certificates, and requires 21 actual semantic
dependencies. It also checks the retained chain from the final negation through
`witness_not_logMajorized`, `witness_largest_strict_gap`,
`witness_strict_norm_gap`, `squaredGap_positive` and `scalar_gap_positive`.
The scalar proof's actual term calls
`LeanCert.Validity.verify_strict_upper_bound_dyadic_checked`, with constant zero
on the singleton interval `[0,0]`, the exact positive gap as bound, precision
`-53` and depth `10`. The defining proof uses `interval_decide (trust := kernel)`;
the pinned verifier's kernel route has no native fallback. This certificate is
consumed in the final result, rather than merely imported or demonstrated.

## Review standards, reuse and attribution

I applied the repository's adaptation of Tau Ceti's correctness, scope, proof
quality, generality, reuse and attribution rubrics at
`afb424eda89e8ac96d9eb69f6a88972055a4cd1b`. The retained rubric files were checked
against cached immutable GitHub tree blob identities. This is not an official
Tau Ceti review or endorsement. The single coherent scope is complete canonical
MI-23; general lemmas discharge its actual prerequisites.

Relevant searches in the pinned Mathlib locate the spectral theorem, complete
root-multiset and determinant identities, `charpoly_mul_comm`, PD congruence and
real-power APIs, and Euclidean/C-star norm identities used in the implementation.
The code reuses these facts. Project wrappers bind independently reviewed
statement definitions and have genuine consumers; this is not proposed as a
new Mathlib compatibility API. The computation is appropriately reduced to
exact small matrix certificates and one scalar sign check, with no interval
search over matrix entries or eigenvalues.

One nonblocking documentation observation: the few `change` steps between
`operatorNorm` and the scoped L2 norm would be easier to maintain with local
comments or an explicit `Matrix.l2_opNorm_toEuclideanCLM` rewrite. I checked the
actual definitional identity and its instance in the pinned library; this is not
a fidelity or trust gap. List-to-multiset conversions likewise preserve the
actual elements and multiplicities. No frozen proof change is needed for this
local approval.

The code and README preserve Matthew J. Colbrook's counterexample and informal
proof attribution, credit reuse of the campaign's CFC/norm patterns and Mathlib,
and identify George Stepaniants as the Lean formalizer with his Department of
Computing and Mathematical Sciences, California Institute of Technology
affiliation. No George email is published. The Apache license and AI-assistance
disclosure are present. The README's pending final-review text can be updated
during candidate packaging; no publication status was changed in this review.

## Reproduction and retained evidence

From this project's `lean` directory:

```
python3 reviews/proof-referee-1-evidence/fresh_review.py
python3 reviews/proof-referee-1-evidence/reconstruct_witness.py
python3 reviews/proof-referee-1-evidence/consolidate_review.py
```

The raw logs, exact commands, environment, source/object hashes, input checks,
pin checks, literal statement signatures, dependency traversal, scalar proof
term, rational reconstruction and inspected-library/rubric hashes are retained
in [proof-referee-1-evidence](proof-referee-1-evidence/).
The fresh inspection log SHA-256 is
`40f23a3dcc2c4002fe214cc1449f81071396590a72a39b12e023f38aacc9bfec`;
the fresh Solution log SHA-256 is
`4411295dabdf60016a069fe6d1238016eafcc75a4746204acb2ed3c54dc0749a`.
[The evidence manifest](proof-referee-1-evidence/EVIDENCE-MANIFEST.json) binds the
report and every retained review artifact. Only this report and its evidence
directory were written. All frozen mathematics, configuration, canonical
targets and statuses are preserved; no commit, push or PR action was performed.
