# IE-03 final reuse, documentation and attribution review

Final review by OpenAI Codex agent `/root/ie03_final_reuse` on 2026-11-09.
I did not implement the proof. **APPROVE** the proof source at
`89987eb5059ce5a497c18ce50c9b86f8cf394b86` for this review scope. The two
documentation corrections below do not require changes to the Lean proof.

The reviewed commit binds the full project, including all five generated
data modules and their check modules. Selected SHA-256 bindings:

| File | SHA-256 |
| --- | --- |
| `Challenge.lean` | `437e360d1c1111a6e39f30048915e1a2f99ac7331f68df2167734eee2d204c00` |
| `Solution.lean` | `c9b3cf81bec5c26197d198973ec0d2e07484bc1fab4d26d14bb9723c2714e7f9` |
| `NLA/IE03/Definitions.lean` | `39934cbfb2bba5eb0b24d3a7d45e8b8123649bbe3467685253240d2f76ad42e8` |
| `NLA/IE03/Path.lean` | `5d88fc46c841883b949adde568cc44945d1f73d4f6d68b8b22b410b74799c960` |
| `NLA/IE03/Lift.lean` | `751cb8d39c2816c77e718af759227d03b54b47526035b742a4a61f5108e48b64` |
| `NLA/IE03/Walsh.lean` | `731108a767e1cdc2f496c13c8d85351907aa4ede68843b9c8577e515970dcde0` |
| `NLA/IE03/Proof.lean` | `d801f8e2cd600fcbbdbb516679e4c2be763148310da972bfcbc0783235edcb37` |
| `NLA/IE03/Certificate/Sound.lean` | `519acb1f00d0165b1b505d4595b848c581691d0996c468dcc8524e1acc997317` |
| `NLA/IE03/Certificate/Checkpoint.lean` | `2a8726efe940c5444e684f5fce4b91753d8934f9e12c40871c45fda992e89383` |
| `generate_checkpoints.py` | `34f94116285269566cee53329fcf055fa7ee7f9f1e673b48baeca6bae23b7c1e` |
| `README.md` | `68d2ee68ede4714e89f04ce1cadfb4ac3a5b0a81f8729f40799cdecb8717c4c4` |
| `formalization.yaml` | `b4f4eff39a3938d91a8a3d9277f77a4320d83a83b5b37d1f8564edee703a6b13` |
| `lake-manifest.json` | `358d7900d88ecc1f14f657c0edd1ef95f05a99056fdc892c83f2f24940da982d` |
| `comparator.json` | `57dc1f8dc1d60862eef53d0dc214b77948fef8714c101365c5411ca698bba5fd` |

## Reuse and proof organization

I checked the Mathlib checkout at the manifest revision
`0df444a360eaa60ab8c11dca51a86af692955474`. Its
`Mathlib/LinearAlgebra/Matrix/HadamardMatrix.lean` supplies
`Matrix.IsHadamard.kronecker` and
`Matrix.IsHadamard.of_mul_conjTranspose`. Those APIs concern typed finite
matrices, unitary entries, and two-sided orthogonality. Reusing them here
would require bridging the frozen real sign and row-Gram predicate and
reindexing the product by the parity order shared by the pivot certificates.
The direct `Walsh.lean` proof covers that parity order in a small module
using Mathlib's finite sums. The Hadamard product in the adjacent
`Hadamard.lean` is entrywise multiplication.

The `Fin.succAbove` embedding in `Mathlib/Data/Fin/SuccPred.lean` is the
bounded-index counterpart of `skip`. The natural-number form in the
frozen statement keeps the integer decoder and its bounds on the same
indices. The block Schur lemmas in
`Mathlib/LinearAlgebra/Matrix/Hermitian.lean` use block matrices and
inverses. They do not supply a proof that each of the two lifted pivots is
maximal over the full active square. I found no complete-pivot path API
that would subsume the local one. The local names are scoped to
`NLA.IE03`, and `Agree` and `Trace` expose precisely the active-square
equality used to compose the certificates.

Mathlib is the single direct package dependency, with immutable
transitive revisions in the manifest. The hand-written sources import
individual Mathlib modules. `Lift.lean` uses `linarith` only for
`|p| ≤ 2 * |p|`. A multiplication monotonicity lemma could remove that
direct tactic import, but the current proof is clear and I do not
recommend changing the reviewed Lean source for that alone.

## Reproduction and trust

The project separates `Challenge.lean`, which imports only the frozen
definitions, from `Solution.lean`, which imports the actual proof.
The Solution module chain runs through the five check modules and the
real soundness lemmas, and it contains no import of Challenge. The
Comparator config exports both exact declarations and allows no
definition holes.

The generator reads the source verifier as bytes, checks its pinned hash,
and extracts the literal pivot pairs by parsing the source AST. It uses
exact fractions to generate 129 checkpoint tables and 124 local checks.
Each table uses one denominator, with signed numerator slots recovered
as unbounded integers. Lean checks the positive denominators and pivot,
whole-square comparisons, and entrywise cross-multiplied transition
identities. The generated theorem text uses `decide +kernel` and the
hand-written soundness and composition lemmas. The Python output is a
reproducible certificate input. The proof uses Lean's checking of that
input. The split between packed data and per-phase checks makes the
generated artifacts traceable, and the repository excludes `.lake/`
build products.

I independently ran `python3 -I generate_checkpoints.py --check` from the
project with Python 3.13.14, checked
`verification/STATEMENT-SHA256SUMS`, ran the repository's
`validate_manifest.py`, and ran `lake env lean Audit.lean` with pinned
Lean 4.33.1 against the local built project. Both exported declarations
reported exactly `propext`, `Classical.choice`, and `Quot.sound`.
I inspected the retained macOS build and axiom log. I did not run a
fresh solution build or the isolated Linux Comparator in this review.

## Documentation corrections

- `formalization.yaml` credits Matias Andia for the source and OpenAI
  Codex for the formalization. The sentence “Andia authored the source
  mathematics” is less precise than the manuscript's Acknowledgements
  (`references/andia-ie03-2026-10-31/main.tex:211–212`). Use wording
  such as “Andia authored the source manuscript, which credits GPT-6
  Astra Pro with finding the counterexample.” Preserve the same
  distinction in the promotion entry.
- State Python 3.10 or later in the project reproduction instructions.
  The generator uses `zip(..., strict=True)` and `int.bit_count()`.
  The Lean build itself consumes the checked-in certificate sources.

The new project license matches the repository's Apache-2.0 template.
The manuscript and verifier remain separately credited and the generator
binds their upstream provenance. This review approves code organization,
reuse choices and reproducibility for the named source revision. The
isolated Linux comparison and the other independent review scopes are
separate promotion evidence.
