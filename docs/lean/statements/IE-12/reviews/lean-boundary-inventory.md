# IE-12 independent Lean boundary review

Reviewer: OpenAI Codex AI agent `/root/inventory`, independent of all specification/implementation authors. Phase: `lean-boundary`. Verdict: **APPROVE**.

ExactRealMachine has fixed finite instruction/label/register syntax and a finite real-constant table. Each running transition performs exactly its scalar instruction with old-state operands. Reads/writes and address arithmetic are charged, the initial dense layout has disjoint matrix/RHS/epsilon locations, and there is no real-to-natural, solver, spectral, digit-extraction or arbitrary evaluator instruction. Quotient/remainder describe only free initial input placement. A successful halt returns the actual memory slice of the original input dimension; it costs a transition. Failure is distinct and both terminal tags are absorbing.

FairBitLaw is the actual half/half Bernoulli law. StreamLaw is the product of the two genuine infinite independent-coordinate laws; explicit probability-measure instances rule out the infinitePi zero-measure fallback. Draw instructions consume only the next coordinate of their own cursor, preserving adaptive independence and preventing unlimited-stream access.

The real Euclidean norms and original A,b residual are explicit. The positive-dimensional sphere supremum is nonempty and bounded. Norm-one A and nonzero returned x make the A-only backward-error denominator positive. CostBound is C*n^2*Real.rpow(epsilon)(-q), with positive real C,q chosen with the program before every input. Every stream realization must make a bounded nonzero return; the same actual return predicate is used in the >=99/100 success event. No expected-time, condition-number, storage or input-distribution relaxation appears.

Operational controls were read for the dense input layout, charged halt, zero-division and negative-root failure, absorbing terminals, separate sequential Gaussian/bit cursors and actual stream probability instance. These controls and their source hashes are bound as additional evidence; they are not a solver or a proof of Target.

The full canonical README equals ORIGINAL.md byte for byte; live/frozen namespace correspondence and complete local imports/pins are bound below. Author-local compilation and identity evidence was inspected against the current source hashes, with zero exits and only standard axioms. This review did not rerun Lean and claims no target proof, newly formalized correspondence lemma, external human review or Linux Comparator result.

## Reviewed input hashes

- `docs/lean/statements/IE-12/IMPLEMENTATION_NOTES.md`: `8fa1fab63fdcbf3005ca94544188ddda2eff18efb54be4a6ef24eb90f7d1a1aa`
- `docs/lean/statements/IE-12/NUMERICAL_TARGETS.md`: `68eb633d1c59347f714d4eab8d32912cdbcd27343ecb50a9dc557741a781cf3d`
- `docs/lean/statements/IE-12/ORIGINAL.md`: `a46926ac2cec003913f0ae71d3f4b54dfb44e82bb90daeaa3ab79ed757421b77`
- `docs/lean/statements/IE-12/source-lock.json`: `8179a06b0dd286ff4b1bec2a127ec8c950cce289e2db8c72a7b456f59933fec0`
- `lean-statements/NLA/Computation/ExactRealControls.lean`: `49c287c46bc3b8de2b6f4e0bef049306965572762c8c02b5d6394e0c33b1f04a`
- `lean-statements/NLA/Computation/ExactRealMachine.lean`: `d96cd036d1b559225f7b861ea0ffed4ebf403d089c431ac0ae8a3482c4b830c8`
- `lean-statements/NLA/Statements/IE12.lean`: `3b87e45a6896f7cf31fed7338265475bb1ced9f8e7c161ccda7ad8f877bb1343`
- `lean-statements/NLA/Statements/Infrastructure.lean`: `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37`
- `lean-statements/Reviewed/IE12.lean`: `02bd169de535a01b877c5d55691a434365767c8e1a9e0246babea7f7fca4904d`
- `lean-statements/lake-manifest.json`: `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8`
- `lean-statements/lakefile.toml`: `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40`
- `lean-statements/lean-toolchain`: `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`
- `linear-systems-and-elimination/IE-12/README.md`: `a46926ac2cec003913f0ae71d3f4b54dfb44e82bb90daeaa3ab79ed757421b77`
