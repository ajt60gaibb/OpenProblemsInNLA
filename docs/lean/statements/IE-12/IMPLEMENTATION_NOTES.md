# IE-12 implementation boundary

Implementation author: OpenAI Codex AI agent `/root/infra_audit`, 2026-09-28. The specification author is `/root/statement_design`. The final specification SHA-256 is `68eb633d1c59347f714d4eab8d32912cdbcd27343ecb50a9dc557741a781cf3d`; the independent `/root` and `/root/inventory` approvals were read and verified before implementation. Neither specification nor implementation authors are eligible to supply the final independent approvals for this target.

## Actual computational model

`NLA.Computation.ExactRealMachine` contains finite instruction syntax, finite program data and an explicit transition function. The fields `extraLabels` and `extraNatRegisters` represent counts minus one, ensuring label zero and natural register zero exist. Scratch-register and constant-pool sizes may be zero. Program code is a finite table from a finite label type to constructor syntax; it cannot inspect an input except through the defined transitions. Fixed natural literals and the finite real-constant table are part of that program.

All real and natural arithmetic, comparisons, sequential draws, memory reads/writes, jumps and halt take one `run` transition. Operands use the old state, including when destination and source coincide. Division checks its denominator for zero; square root checks for a negative operand. These cases produce the failed tag. Failed and successfully halted states are absorbing. The successful tag stores an ordinary natural output address, and `output` returns the actual memory slice of the original input dimension, even if the program has overwritten its input-size register. The initial running state cannot return an output at time zero, and setting a return address without executing halt cannot satisfy the return predicate.

`inputMemory` explicitly decodes the initial dense matrix, RHS and tolerance locations, defaulting to zero elsewhere. Quotient and remainder in this *initialization definition* describe the given input layout; they are not executable instruction constructors. There is no real-to-natural conversion, floor, logarithm, digit extraction, factorization, solve or arbitrary evaluator instruction. Only a finite number of cells can be changed by a finite sequence of scalar writes.

`FairBitLaw` is the actual `bernoulliMeasure true false` with parameter exactly `1/2`. In the pinned API, this is half a Dirac mass at each of the two Boolean values. `StreamLaw` is the product of `Measure.infinitePi (fun _ : Nat => gaussianReal 0 1)` and `Measure.infinitePi (fun _ : Nat => FairBitLaw)`. The Gaussian parameters are mean zero and variance one. Actual `IsProbabilityMeasure` instances are elaborated for the fair-bit and stream laws, avoiding the zero-measure fallback in `Measure.infinitePi` when its arguments are not probability measures. `infinitePi` has the prescribed independent finite-coordinate product marginals; the outer `prod` supplies independence of the two streams. The two draw constructors increment only their own sequential cursor.

## Target and exact mathematical quantities

`IE12.Target` quantifies one finite program and positive real `C,q` before every dimension, input and draw. It uses the exact real exponent `Real.rpow epsilon (-q)`. Every draw must reach a successful nonzero return within the stated real bound on the integer transition count. The probability event uses that same bounded return, then checks the full original residual against the original `A` and `b`. Probability is compared in nonnegative extended reals with `ENNReal.ofReal (99/100 : Real)`.

Vector norm is the nonnegative square root of the full sum of squared coordinates. Spectral norm is the real supremum of the output Euclidean norm over vectors whose sum of squares equals one. In the positive finite-dimensional target domain this set is nonempty and bounded, so it is exactly the induced Euclidean norm. The normalized nonsingular matrix promise and nonzero returned vector give a strictly positive error denominator. No arbitrary norm predicate, matrix-product oracle or input-conditioned distribution is assumed.

The fixed finite syntax and concrete step function ensure each finite trace depends measurably on finitely many sequentially consumed coordinates. The target's existential vector is the uniquely determined returned memory slice; it is not an arbitrary chosen solver. The success set can therefore be written as the countable union over bounded natural trace lengths of the corresponding measurable finite-trace error events. These correspondence facts remain part of independent mathematical review; this implementation does not claim formal measurability lemmas or a solver-correctness proof.

## Mechanical evidence and its scope

The pinned Lean `4.33.1` compiler and manifest-matching package sources were used for direct development elaboration. The live target passes `#assert_statement` and `#assert_trust kernel`, with its printed axiom closure exactly `propext`, `Classical.choice`, `Quot.sound`.

`NLA.Computation.ExactRealControls` contains kernel-checked controls for the complete two-dimensional input layout; a two-step trace that sets an address and then pays for halt; division-by-zero failure; negative-square-root failure; absorption of both terminal states; the sequential draw order `Gaussian 0, Bit 0, Gaussian 1`; and the actual stream probability-measure instance. All controls have explicit kernel trust checks. They test the operational boundary, not a solver or the catalog proposition. The controls should be included in the shared CI build/import list.

Development build output and receipts are under `/private/tmp/nla-ie12-evidence`, with object files outside the source tree under `/private/tmp/nla-ie12-build`. A portable package build is `lake build NLA.Computation.ExactRealControls NLA.Statements.IE12 Reviewed.IE12` from `lean-statements/` after resolving the checked-in pins. No numerical sampling, floating-point experiment or native decision trust was used.

The independently frozen per-ID source retains separate definitions of the target and its mathematical predicates. The reviewed computational model is shared, because independently renaming its inductive instruction and program types would create distinct types; the complete model source belongs to both import closures and must be bound by each final independent review's hashes. Target identity checks compare the two per-ID boundaries; source/import hash gates detect changes to shared semantics. Neither mechanism proves IE-12. The archived Sidney Holden algorithm, authorship, Solved status and prior-source credit are unchanged.

| Source | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Computation/ExactRealMachine.lean` | `d96cd036d1b559225f7b861ea0ffed4ebf403d089c431ac0ae8a3482c4b830c8` |
| `lean-statements/NLA/Computation/ExactRealControls.lean` | `49c287c46bc3b8de2b6f4e0bef049306965572762c8c02b5d6394e0c33b1f04a` |
| `lean-statements/NLA/Statements/IE12.lean` | `3b87e45a6896f7cf31fed7338265475bb1ced9f8e7c161ccda7ad8f877bb1343` |
| `lean-statements/Reviewed/IE12.lean` | `02bd169de535a01b877c5d55691a434365767c8e1a9e0246babea7f7fca4904d` |
