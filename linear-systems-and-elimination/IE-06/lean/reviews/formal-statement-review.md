# Independent review of the IE-06 formal statements

Date: 2026-10-06. Reviewer: independent mathematical-review agent.
Review type: source-level mathematical fidelity and declaration audit.
This is not an execution receipt or a proof of the random-matrix theorem.

## Reviewed bytes

| File, relative to `IE-06/lean` | SHA-256 |
| --- | --- |
| `NLA/IE06/Definitions.lean` | `a5a8bf8d4a9f6dc97d0b645a4ed7639ee808ae4d340dc70c913e06ed5057c19a` |
| `NLA/IE06/Statements.lean` | `4bdb38cf65e1ab8859efd45946a7de346f1a3ed93454be926fc0b4406a735c7b` |
| `Challenge.lean` | `701de729aceba6a69c72440c030b98c686942571b7f0160c84bdd9b95ceecbda` |
| `comparator.json` | `de4f4300a69054519964694f6228084cd063e843b3a29ec1815348ac493f4d6a` |
| `reviews/statement-specification.md` | `c58ae67bbbd2d9764c75924eec6a400e23d65e90ccbc2257ead8db01ec24592b` |

I read all four files, compared the definitions against the preimplementation
specification and original canonical problem, and inspected the reused IE-04
definition source independently. Approval below applies to the recorded bytes.

## Mathematical findings

`Mat n` is the actual real matrix space on `Fin n × Fin n`.
`gaussianMatrix n` is the nested finite product of `gaussianReal 0 1` measures,
so it specifies mutually independent standard Gaussian entries rather than
postulating an unspecified random input. Its measure-valued target retains
the original probability, with no real conversion, truncation, or conditioning.

`rowSwap` swaps current row positions and never columns. `AdmissiblePivot`
requires a row in the active block, a nonzero entry, and an absolute-value
maximum over all active rows in the current pivot column. Its comparisons
permit equality, so every maximum-magnitude tie choice is covered.
`schurStep` has the exact real rank-one update on the next active block.
The swapped diagonal denominator equals the selected nonzero entry on an
admissible path. Zero-padding outside the active block cannot contribute to
`activeMaxNN` because that maximum independently restricts both active indices.

`trajectory` begins with `A` and performs the selected update once per stage.
`growth` takes the maximum for `k : Fin n`, hence exactly stages zero through
`n-1`. Those include the input and the final scalar complement. The later
zero matrix after the final elimination is not substituted for that complement.
Measuring a stage before its active row swap gives the same maximum as
measuring after it. The denominator is the maximum absolute entry of the
original matrix and is positive for a nonsingular positive-dimensional input.
No LU multiplier or stored eliminated entry is counted.

`exceedanceEvent n t` explicitly requires positive dimension, a nonsingular
input, and existence of an admissible path whose growth is strictly greater
than `t`. Thus its complement controls every admissible tie path. The `0 < n`
guard resolves the preimplementation empty-dimension concern for every real
threshold. Singularity is excluded in the event itself; the Gaussian law is
not conditioned on nonsingularity. For dimension one, every nonsingular input
has just one active scalar and the mathematical growth ratio is one. These
dimension conventions do not change the asymptotic target.

`SquareRootUpperBound` retains the complete original quantifiers:
every positive real `η`, the actual Gaussian event at real threshold
`n^(1/2 + η)`, dimension tending to infinity, and probability tending to zero.
It does not replace this with a fixed exponent, eventual boundedness, a finite
range, a matching lower bound, or a claim about floating-point elimination.
The probability values lie in `ℝ≥0∞`, where convergence to zero expresses the
same intended probability limit.

`SchurSubpolynomialTail` is separate. It quantifies over every positive `α`,
then positive `C` and a natural cutoff at least two, and finally all dimensions
beyond that cutoff. Its threshold is `sqrt n * exp(C * sqrt(log n))`; its
strict probability bound is `ofReal(n^(-α))`. The constants are outside the
dimension and matrix quantifiers. The comments correctly distinguish this
all-Schur extraction from the literal LU-growth statement in Theorem 1.4 and
identify the unformalized source, normalization, and tie bridges.

## Proof status and Comparator configuration

`Definitions.lean` and `Statements.lean` contain definitions, not an assumed
source theorem. Their kernel-trust assertions do not convert a `Prop`
definition into a proof of that proposition.

`Challenge.lean` contains precisely six deliberate `sorry` declarations:
the two probabilistic targets, probability-measure status, event measurability,
admissible-path existence for nonsingular matrices, and Gaussian nullity of
the singular locus. Each signature expresses the intended mathematical
obligation. The file itself clearly labels them unproved and requires any
future solution to avoid importing the placeholder module.

These placeholders are not mathematical results. In particular, the path
existence and measurability properties are exposed instead of being silently
declared accomplished. A future proof still needs to establish them and the
random-matrix estimate. No full solution is present in the reviewed files.

`comparator.json` lists all six challenge targets exactly once. Its
`definition_names` is empty, as required by the shared repository protocol,
so it provides no replaceable definition holes. The permitted axioms are only
`propext`, `Classical.choice`, and `Quot.sound`; neither `sorryAx` nor native
evaluation axioms are allowed. Actual rejection/acceptance behavior requires
the separate execution checks recorded by the infrastructure work.

## Preservation and disposition

The three canonical file hashes still match the author's initial snapshot:

| Canonical file | SHA-256 |
| --- | --- |
| `README.md` | `15b987cd776e9a4483fd9b8dabd15c945ac5fe4898b7231c6b2f3269a731d523` |
| `problem.tex` | `b73d3f78fdbce9badb64eae1193eb8813b39ef27841426b6b4688b5e9e90a5b5` |
| `problem.pdf` | `dc97a3d6c063848893e23e360af918357c7952375f9ad62424e9be49c3ef1668` |

No mathematical fidelity defect was found in the reviewed Lean statements.
**Approved as a statement package, not as a completed proof.** I also read the
author's finalized specification at the hash above. It resolves both earlier
alignment requests, accurately states the direct extended-real `Tendsto`
target, and records the exact infrastructure fixture separately. It is
approved. Any added conditional implication or numerical proof requires a
follow-up review of its actual declaration and dependencies.
