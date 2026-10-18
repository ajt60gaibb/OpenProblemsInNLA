# SP-11 canonical completed proof — second independent approval

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I did not implement the canonical package wrapper or its source-copy packaging.
**Verdict: approve the full unchanged target in the canonical package at the
hashes below, with fresh local kernel evidence. Linux verification is pending.**

Package: `eigenvalues-and-inverse-problems/SP-11/lean`.

| Export/boundary | SHA-256 |
| --- | --- |
| `Solution.lean` | `c0b7763486eb9f825104cab619e4151d7b91897a3e70719251d772744c047478` |
| `NLA/Proofs/SP11/Final.lean` | `de7bfb35944fb25d0d7b8a15b7f7331fa942922b79a6af79e4c285dfa071840a` |
| `NLA/Statements/SP11.lean` | `7de112a24cb0b78894d495b840a77a58572cce574d5d77eda15381410c65b131` |
| `Reviewed/SP11.lean` | `3a294de54f52a4287ed22b80d5b0721859154b642fe3c1ac62f7d4609be38222` |
| `Identity.lean` | `942bdf685279cd9b9182367e00fac3428204490d05747e8172d353349c4dc0b9` |
| `comparator.json` | `bac828f2e95d7135346e5a48dbd07dbd65450b843860f4849739dca3c69ca2fe` |

`Solution.lean` directly discharges the zero-parameter theorem
`NLA.SP11.target : NLA.Statements.SP11.Target` using the copied complete
shared proof. It imports no Challenge placeholder. The exact live/reviewed
statement and original canonical page retain their published bytes; Identity
remains a definitional equality. Comparator selects only the full target,
with no definition holes and only standard foundational axioms permitted.
There is no weakening to a supplied representation, order, noncancellation
condition, restricted graph class, PSD requirement, or prescribed diagonal.

The independent copy check passed **64 checks**: all 38 copied local modules
(36 proof modules and two statement/infrastructure modules) match their
reviewed shared sources byte for byte; the complete NLA file set is exact;
the current export lock matches; historical statement/configuration hashes
are preserved; and the live/reviewed statement and original canonical page
match published base `47006df8b3a6c724a557266c891893d03e69323a`.
The historical scaffold Lake file is retained separately while the current
Lake configuration properly builds Solution and Identity.

The independent mathematical review of the identical proof closure is
`CLOSURE_REVIEW_2_2026-10-18.md`, with separate hash-bound diagonal, edge,
class-weight and support reviews. It proves nonzero actual Gram coefficients
for every required edge/diagonal, specializes all required polynomials at one
real assignment, applies the Gram rank bound, and transports the witness
through the actual greedy permutation to the original graph. No mathematical
source theorem is assumed as an axiom.

Fresh canonical-source verification passed **42 Lean commands**: all 36 proof
modules, the live statement and infrastructure, the frozen reviewed statement,
Solution, Identity, and a separate consumer. All **291 explicit named
declarations**, including **201 theorem/lemma constants**, pass theorem-kind
checks where appropriate, LeanCert kernel trust and transitive axiom checks.
The consumer additionally requires `NLA.SP11.target` to have the literal
unchanged Target type, with no extra parameters. Both that export and the
shared target depend only on `propext`, `Classical.choice`, and `Quot.sound`.
All frozen sources remained unchanged and all ten dependency pins/tracked
sources passed before and after.

```bash
python3 docs/lean/campaign-2026-10-17/verification/check-sp11-canonical-copy.py
python3 docs/lean/campaign-2026-10-17/verification/check-sp11-tree-color-support.py \
  --project eigenvalues-and-inverse-problems/SP-11/lean \
  --root-module Solution Identity --target-theorem NLA.SP11.target \
  --evidence-name sp11-canonical-full-target-review
```

Machine-readable evidence is in
`docs/lean/campaign-2026-10-17/verification/sp11-canonical-copy-check.json`
and `sp11-canonical-full-target-review/`. The latter retains exact source,
consumer, compiler/driver identities, dependency checks and raw logs, and
records full local target proof with Linux Comparator false. Sources were
compiled into a fresh private output prefix, excluding the existing canonical
and shared project objects; pinned compiled dependencies were reused.

Five transitive support modules are my implementations; their independent
source reviews are by other agents. I claim runtime audit, not independent
self-review, for those supports. No proof or package source was changed for
this review. This is AI-agent review and local macOS LeanCert kernel evidence,
not external human review or real Linux Comparator acceptance. The latter
must be bound to the committed final package and recorded separately.
