# Independent fresh PR366 Linux artifact audit — 23 October 2026

Reviewer: OpenAI Codex AI agent `/root/verification`, author of none of these
proofs. **PASS: 126/126 checks**, including all **325 package inputs**, **183
Lean inputs**, and **171 reviewed shared-source/package-copy pairs** for the
three complete original Targets.

The authentic successful [workflow run 39995308565](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39995308565)
belongs to PR366 head `cc8f375f3d79ce7d3b7053526638ed37c9125e92`. Its jobs
actually checked synthetic merge `738e828fef5095e6f782a14bc68783a49a35212b`.
The Git merge parents are exactly published base
`5487945e5a72abd952b0c89915915de8cc9b3e65` and that PR head. The authentic
run metadata and fresh GitHub connector observations retain the head identity;
each raw checkout log and harness result retains the executed merge identity.
Both identities are explicitly checked and remain distinct. No metadata was
rewritten, and the older head-equals-execution checkers were not bypassed or
presented as passing this different situation.

| Full original problem | Actual successful job | Artifact ID | Exact package / Lean inputs |
| --- | --- | --- | --- |
| PF-05 | [120557399423](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39995308565/job/120557399423) | `12519698144` | 90 / 46 |
| SP-12 | [120557399244](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39995308565/job/120557399244) | `12520885067` | 96 / 55 |
| TR-14 | [120557399236](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39995308565/job/120557399236) | `12519239053` | 139 / 82 |

All three original ZIP digests match fresh GitHub artifact metadata, the original
raw upload logs and the retained bytes. I independently checked archive
path/symlink safety, extracted each original ZIP and matched every member with
the retained extraction. Each artifact contains 15 files. The immutable original
ZIP SHA-256 values are:

| Problem | SHA-256 |
| --- | --- |
| PF-05 | `cb0064e0388bb40708540a807c8f9174898c88fd51f2acf6ed0ec63638d8f306` |
| SP-12 | `bd452c46cd5657badc5aaaec474d1d6c913e8b18d704bef416fc30c849af8e69` |
| TR-14 | `d4d99a9ce55b75a7bea237995c522377b2fae305505ec510fdcb4e3b2411e265` |

Each actual harness result says `comparator-accepted` and
`lean_cert_proof_trust: kernel-checked`. Each selects only its actual full
theorem (`NLA.PF05.target`, `NLA.SP12.target`, or `NLA.TR14.target`) in separate
Challenge/Solution environments, with no definition holes. The real exporter
exports those names from both environments, Comparator's default Lean kernel
accepts the solution, and its final acceptance marker is present. I reproduced
the generated theorem-kind/LeanCert consumer from the actually executed
committed harness; every consumer hash agrees with its actual receipt. Each
consumer enforces a proved theorem constant and kernel trust. The actual printed
full-proof axiom closure is exactly `propext`, `Classical.choice`, `Quot.sound`.

Each of the three actual jobs also contains the full real Linux sandbox and
negative-control evidence: honest inductive/quotient replay accepted, invalid
raw proof rejected, quotient postcheck mismatch rejected, all five Comparator
regressions passed, actual sorry/native axioms rejected, and all four unsupported
sandbox-option cases rejected. The sandbox logs establish the separate build/
export write policies, denied outside and symlink writes, private namespaces,
host-network/AF_UNIX denial, absent effective capabilities, `no_new_privs`, and
nested-write rejection. All required dependency, service, comparison, LeanCert
build and consumer exit statuses pass. Manifest-validation and isolation setup
steps are successful in the observed actual jobs. The separate top-level
checker-controls job was skipped; it is not claimed as a pass. Required controls
were genuinely executed inside each of the three proof jobs.

The source correspondence is exact at four boundaries: actual executed merge,
PR head, current integration package and previously independently reviewed
integration commit `42d1665800d0185581149ef494e03055b533d636`. All 325 hashes
and exact tracked file sets agree. All 183 Lean inputs remain identical to those
earlier reviewed sources. All 171 shared-source/package-copy pairs match their
locked review hashes. The checker source lock, Forsythe revision, Linux
Lean4.33.1 compiler commit, reviewed LeanCert/Mathlib pins and recorded checker/
exporter/sandbox binary identities pass without relaxing a guard.

I checked each literal original Target definition and closed final export. These
are the full PF-05 rigidity/uniqueness equivalence, SP-12 PSD/Strong Arnold
chromatic-nullity theorem, and TR-14 all-width ordinary/symmetric Hankel-rank
equivalence. No conditional support gate or definition/Identity elaboration is
substituted for a complete proof. Their mathematical-source reviews remain
applicable because the proof and statement bytes are identical. This evidence
adds fresh actual integration CI to those existing reviewed proofs; it does not
claim every other Solved problem is now formalized.

The permanent-ID registry remains byte-identical to published original base
`36767fa430309f13d04dc6ebe080d470f5c2444a`, with all canonical paths present.
The three canonical pages, original statement snapshots and all 13 original
archived README/TeX/PDF/manuscript objects remain byte-identical to the prior
independent preservation audit's inputs. That earlier 33-check audit and its
receipt hash are bound by this new machine-readable report; original mathematical
text, attribution and history remain preserved.

Original archives, gzip-compressed raw logs, exact extractions, generated
consumers and per-problem `audit.json` reports are retained in the three problem
subdirectories here, outside the frozen canonical packages. Fresh connector
metadata and unchanged authentic run metadata are retained at this directory's
root. `result.json` binds all observations, checks, source identities and hashes.
Reproduce from the original working checkout with:

```bash
python3 reviews/2026-10-23-solved-lean/latest-candidates/fresh-pr366-ci/audit.py \
  --repo /Users/ajt253/.codex/worktrees/solved-lean-integration/OpenProblemsInNLA
```

This is a fresh independent audit of actual completed Linux artifacts, not a
local Linux rerun or external human review. No proof/package byte, shared
safeguard or canonical source was changed during the audit.
