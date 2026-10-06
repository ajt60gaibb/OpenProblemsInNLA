# Independent review of local verification infrastructure

Date: 2026-10-06. Reviewer: independent mathematical-review agent.
This is an independent source and retained-evidence review, not another
authoritative Linux sandbox run.

## Reviewed bytes

| File, relative to `IE-06/lean` | SHA-256 |
| --- | --- |
| `verification/check_local.py` | `da4e6d625399074ad8923f7a06f911de1f184646acdd4350445e4f6bb1fe2dee` |
| `verification/check_comparator_core.py` | `1af77aaa08f87d90168d2da384f8da01cb406b0a10f8f300153dfcf82dc58d71` |
| `INFRASTRUCTURE.md` | `7ba1654f3d79396dc7fdeb52353c746f7a247f1c8176c61ca2383b43b6ddd6ee` |
| `NLA.lean` | `02493f578226d478d3b9fd743a59560343c50cea819b7e282abcffee3dd795e2` |
| `lakefile.toml` | `c08b0b52b55aab01f9a77ec88e2a61285a893204e30343e1ce5f5db954c3a21e` |

## Local statement checker

The checker compiles copied project source into a fresh temporary output
directory, checks the runtime version and dependency revisions, records source
and log digests, and removes its own temporary compiled outputs. It explicitly
trusts the prebuilt dependency cache; checking source revision/cleanliness
does not independently establish the provenance of that compiled cache.
The script and documentation disclose this limitation.

The axiom pass inspects all declarations owned by concrete project modules,
including generated auxiliary declarations. Only `propext`, `Classical.choice`,
and `Quot.sound` are permitted. `Challenge` is separately elaborated as a
reference interface and excluded from verified proof products. Concrete
modules are checked for importing it, and transitive axiom checking would
reject use of its placeholder proofs. Deliberate `sorry` and `native_decide`
fixtures must fail with the corresponding trust-check rejection messages.

I requested one reproducibility correction: the original checker copied a
source file and then recorded the live source's digest. An edit between those
operations could make the recorded digest differ from the tested snapshot.
The final version instead records the copied bytes, immediately checks live
source equality, and later checks unchanged live inputs against that digest.
The correction is present at the reviewed hash.

I examined the final completed run
`verification/local/attempt-bpcivixz/result.json` and its logs. It reports success
and an audit of 42 concrete local declarations with permitted transitive
axioms. The report explicitly denies an IE-06 proof and full Comparator
execution. I independently recomputed every command-log digest and every
recorded copied-source digest; all match the receipt and current inputs.
This run covers the mathematical modules, supporting proofs, and `NLA.lean`
umbrella. The latter merely imports the reviewed semantic and conditional
modules and excludes Challenge. The final script hashes above match the
executed source snapshots and receipts.

## Comparator core fixtures

The separate core checker copies exact source-lock-matched upstream
`Compare`, `Axioms`, `Util`, and exporter parsing modules, preserving their
license. It calls the unchanged comparison and axiom-checking APIs on separate
fixture environments. It does not replace the upstream comparison algorithm.

I inspected the final successful fixture receipt and full runner output in
`verification/comparator-core/attempt-077ld6ey/`. All nine assertions pass:
matching theorem/definition acceptance, allowed-axiom acceptance, different
theorem-type rejection, changed-definition-meaning rejection, theorem-to-axiom
kind rejection, and separate matching-type/prohibited-axiom checks for both
`sorry` and native execution. The final native rejection test checks the actual
native-decision axiom prefix. Every retained command-log and source-snapshot
digest matches its receipt on independent recomputation; the executed script
digest also matches the current reviewed helper.

These checks execute real Comparator library code. They do not execute the
full Linux Comparator process, the exporter, Landrun/Bubblewrap, or raw kernel
replay, and they do not compare a completed IE-06 solution. The receipt and
documentation accurately preserve those boundaries.

## Disposition

**Approved for the stated local development scope.** The shared authoritative
verification gates remain separate; the reviewed code does not count
Challenge placeholders or fixture successes as a mathematical proof.
The conditional and semantic theorem approvals are in
`proof-support-review.md`, and the complete original statement approval is in
`formal-statement-review.md`. No unconditional IE-06 proof or successful
authoritative Linux/CI run follows from these checks.
