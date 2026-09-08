# Standing Rules for the Proof and Lean Project

The repository is the durable project state. Chat memory and older handoffs may
help, but they do not override the current mathematical record. Older chat
messages and past Pro responses are context, not a pending task queue.

## 0. First launch: instantiate and begin

If `PROBLEM.md` still contains `UNINITIALIZED TEMPLATE`, use the current Goal as
the source of the project objective. The user should not have to edit template
files before mathematical work starts.

On first launch:

1. write a faithful, precise `PROBLEM.md`, including the requested deliverables;
2. infer whether the current focus is `PROOF`, `LEAN`, or `JOINT` and initialize
   `PROGRESS.md` from the actual repository contents;
3. preserve useful existing files in `proof/` and `lean/`;
4. commit and push the initialized project; and
5. begin the requested work immediately.

Keep initialization brief and substantive. Do not build setup scripts,
questionnaires, schemas, validators, empty directory trees, or project machinery
for its own sake. Resolve minor ambiguity by a faithful workable interpretation.
Ask the user only when no reasonable interpretation preserves the intended
objective. Create the Google review Doc only when the first Pro review is
actually opened.

## 1. One target, two cooperating workspaces

- `proof/` contains the human-readable theorem development, TeX, notes,
  computer-assisted proof code, exact data, and proof-bearing certificates.
- `lean/` contains the Lean statement, proof, certified numerical work, and
  optional high-assurance verification machinery.

`PROBLEM.md` is the canonical mathematical target. The active Goal determines
the requested deliverables and immediate focus:

- **PROOF:** prioritize the mathematical proof and any necessary CAP in
  `proof/`. Do not initialize or maintain Lean merely because the folder exists.
- **LEAN:** prioritize faithful formalization and proof in `lean/`, using
  `PROBLEM.md` and relevant `proof/` material as the mathematical source.
- **JOINT:** develop both tracks together and use each to expose weaknesses or
  simplify the other.

Focus is a priority, not a wall. A proof-focused agent may use Lean when it has a
real chance to clarify or advance the mathematics. A Lean-focused agent may
repair or extend the human-readable proof when formalization reveals a genuine
gap. Do not do substantial work in the inactive track merely for symmetry,
completeness of the template, or appearance.

When working materially inside `lean/`, read and follow `lean/AGENTS.md`. Its
rules protect statement fidelity and Lean's trust boundary; they do not prescribe
a particular proof strategy.

A later explicit user Goal may change or expand the requested deliverables.
Update `PROBLEM.md` and `PROGRESS.md` accordingly. Do not treat the first focus
as permanent when the user has clearly changed the objective.

## 2. Fixed target, free mathematical strategy

Do not silently weaken, replace, or redefine the target or completion criterion.
If the statement is ambiguous, inconsistent, or appears false as written,
identify the issue and pursue the most faithful useful resolution.

`PROGRESS.md` is a living mathematical map, not a contract. Strategies,
notation, file layout, decomposition, named routes, and intermediate obligations
are provisional. Codex and Pro may reformulate the problem, introduce new
representations, combine or abandon routes, use formal tools, or replace an
informal argument by a cleaner one when that advances the exact target.

Use milestones, checklists, and separate notes when they clarify real work. Do
not force them when exploratory mathematics is better served by a looser record.

## 3. Mathematics first, with room for sound judgment

The primary criterion for any action is its expected contribution to the
mathematical objective. Do not substitute engineering activity, process
ceremony, or easy-to-report output for proof progress.

Before substantial support work—tests, checkers, reruns, harnesses,
scaffolding, refactors, packaging, or repository maintenance—silently ask:

1. What mathematical uncertainty, correctness risk, or proof-bearing artifact
   can this address?
2. Could the result change the proof, expose an error, increase justified
   confidence, or make an essential computation auditable or reproducible?
3. Is the scope proportionate to that purpose?

No written justification or permission request is required. The action need not
be guaranteed to succeed; a reasonable chance of resolving a live uncertainty
is enough. If there is no plausible proof-bearing purpose, skip it and return to
the mathematics.

Appropriate methods include, without limitation:

- direct proof, reformulation, examples, and counterexamples;
- symbolic, rational, algebraic, combinatorial, or exact computation;
- numerical exploration that distinguishes mechanisms or locates a rigorous
  route;
- interval arithmetic, certified numerics, and exhaustive finite verification;
- Lean or another formal system;
- literature and source verification;
- targeted testing, code audit, or independent reproduction of proof-bearing
  computation;
- an independently written verifier when it adds real mathematical confidence;
- localized refactoring that exposes logic, removes a correctness risk, or
  enables audit and reproduction.

Creating a lemma file, scratch calculation, focused script, formalization, exact
data file, or small local tool is appropriate when it is the natural vehicle for
mathematical work. The restrictions target process for its own sake, not useful
proof artifacts.

Normally avoid the following when they are routine or generic:

- broad test suites, linting, coverage, CI, and repository-health campaigns;
- generic checkers for the template, bridge, packaging, or file layout;
- unchanged reruns performed only for reassurance;
- wrappers, dashboards, manifests, logging systems, and infrastructure built
  speculatively “for later”;
- archive and packaging validation unrelated to the mathematical deliverable;
- duplicate verification layers with no independent mathematical value;
- refactoring or cleanup unrelated to correctness, auditability, or the next
  proof step;
- ceremonial status reports and communication bookkeeping.

These are not categorical bans. A targeted unit test, clean rerun, independent
implementation, broader audit, or packaging check is appropriate when the
mathematical risk or completion criterion genuinely requires it. Start with the
smallest informative scope, but expand when evidence shows a wider check is
needed. Lean elaboration and theorem builds are themselves proof work, not
“generic testing,” when the Lean track is active.

When several actions are available, prefer the one with the greatest expected
mathematical information or progress toward the current Goal.

## 4. Hashes only for individually locked CAP artifacts

Routine checksums are forbidden. Do not generate, request, compare, save, or
report cryptographic digests, CRC reports, archive-integrity reports, or hash
manifests for repositories, directories, communication, handoffs, packaging,
logs, routine outputs, Lean source, build products, or general file collections.

The sole exception is an **individually named, stable, indispensable,
proof-bearing product of a computer-assisted proof** whose exact bytes need to
remain fixed. Several files may be locked only when each independently has a
specific theorem-bearing role. The file must be handled alone, never through a
directory, glob, repository, manifest, or packaging bundle.

Typical examples are a final interval certificate, exact witness, formal proof
object exported as a stable artifact, or generated table cited by the proof.
Source code and ordinary output are not locked merely because they exist. Lean
source is verified by Lean and versioned by Git; it normally should not receive
a hash sidecar.

Use only:

```bash
python3 .codex/hooks/proof_artifact_hash.py lock PATH --reason "precise mathematical role"
python3 .codex/hooks/proof_artifact_hash.py verify PATH
```

This creates an adjacent `.proof.sha256` sidecar. It detects accidental byte
changes but does not physically prevent editing. If the artifact needs a genuine
correction, create a clearly versioned replacement, update the mathematical
references, and lock the replacement only when stable.

Direct uses of SHA, MD5, BLAKE, `cksum`, `git hash-object`, Python `hashlib`, or
similar tools for integrity work remain forbidden. Do not evade a blocked
operation through another command, language, agent, or tool. Ordinary Git object
identifiers are incidental and are not mathematical evidence.

## 5. Mathematical evidence and confidence

Keep `VERIFIED`, `PARTIAL`, `CONJECTURE`, and `REFUTED` distinct. Preserve
important derivations, examples, witnesses, counterexamples, proof-bearing
computational outputs, exact obstructions, and useful reasons for abandoning or
reviving a route.

Update `PROGRESS.md` when the mathematical picture, focus, or completion status
changes meaningfully, not after every action. Record durable mathematics rather
than activity logs.

A final claim requires a target-specific adversarial audit of assumptions,
quantifiers, edge cases, circularity, dependencies, and every claimed
implication. For computer-assisted or Lean components, the audit may include
targeted tests, formal checking, independent verification, or clean
reproduction. It does not require a generic repository-wide campaign.

The Lean completion standard is set by the current Goal. A routine Lean proof
requires the intended theorem to be faithfully stated and proved with no
proof-side hole. A publication-grade or independently verified formalization may
also require the optional audit and Comparator machinery in `lean/`. Do not
silently claim the stronger level when only the ordinary level has been met.

## 6. Subagents

Use subagents when independent or parallel work is likely to improve the
mathematics. Suitable tasks include derivations, counterexample searches,
literature checks, formalization, Mathlib search, proof-code audit, independent
reproduction, adversarial review, or comparison of genuinely different routes.

Give each subagent a clear mathematical purpose and ask for concrete findings.
Do not use subagents merely to manufacture reports, scaffolding, packaging,
repository-health work, or routine checksums. Avoid conflicting parallel writes
and synthesize confirmations as well as objections when they materially affect
confidence.

## 7. Codex and Pro roles

Codex is the primary proof builder and the sole routine writer of the GitHub
repository. Pro is an independent mathematical reviewer and collaborator: it
reads the repository, checks the requested work without trusting Codex's
conclusions, and writes its response directly to the shared Google review Doc.

Codex may accept, adapt, combine, or reject Pro's suggestions according to the
mathematical evidence. For every material objection, repair it, keep it visibly
open in `PROGRESS.md`, or preserve a concise mathematical reason it is invalid.
No separate disposition bureaucracy is required.

For a Lean-focused request, Pro should read `lean/AGENTS.md` and inspect source
fidelity as well as Lean proof logic. Pro need not pretend to have run Lean when
it has only read repository files. It may request one targeted build, trace, or
piece of evidence through the review Doc when that is necessary; Codex runs it,
updates the project, and continues the same bridge.

## 8. Minimal communication protocol

The normal path is:

```text
Codex -> private GitHub -> Pro -> Google review Doc -> Codex
```

### First review

When Codex opens the first Pro review and `BRIDGE.md` still contains its
placeholder, infer the repository name from Git and create the native review Doc
through the connected Google Drive plugin. Record the URL in `BRIDGE.md` and
push it with the open request. Ask the user for a blank native Google Doc URL
only when the create action or permission is genuinely unavailable. Do not
create the Doc earlier merely as setup.

### Codex opening a review

Keep one current request in `PRO_REQUEST.md`. Identify its focus as `PROOF`,
`LEAN`, or `JOINT`; include the coherent questions and best starting files. The
listed paths guide retrieval but do not prevent Pro from following dependencies.

Before opening a review, push the request and all referenced work. Prefer the
default branch. If the relevant state is on another branch, name it explicitly.
Codex need not freeze useful work while Pro reviews; revise or supersede a stale
request if the mathematics changes substantially.

After pushing, print this complete message with the actual repository name and,
when needed, branch:

```text
@GitHub @Google Drive Review the open PRO_REQUEST.md in OWNER/REPOSITORY as the independent Pro mathematical referee. Follow AGENTS.md, BRIDGE.md, and any workspace-specific AGENTS.md named in the request. Write the substantive response to the linked Google Doc.
```

Do not ask the user to summarize, copy, upload, download, or carry any request,
review, code, certificate, or evidence.

### Pro answering

Pro answers only the current request when `PRO_REQUEST.md` has `Status: OPEN`.
If its status is `APPLYING` or `CLOSED`, do not append another answer to that
request unless Codex opens a new request number.

Pro reads `AGENTS.md`, `PROBLEM.md`, `PROGRESS.md`, `BRIDGE.md`, and
`PRO_REQUEST.md` from GitHub, plus `lean/AGENTS.md` for Lean work. Start with the
material named in the request and follow whatever dependency a sound answer
requires.

Append the response to the exact Google Doc in `BRIDGE.md`. If blank, begin with
`# Pro Reviews`. A compact structure is usually enough:

```text
## Response to Request N

Focus and scope: [what was actually checked]

Verdict: ACCEPT | REVISE | NEEDS EVIDENCE | STRATEGY

[Mathematical or formalization reasoning, concrete repair or route, and only the
additional work genuinely needed.]
```

Adapt the structure when the mathematics calls for it. Do not turn the response
into communication bookkeeping. After updating the Doc, tell the user only that
the response was written; never leave the substantive review solely in chat or
ask the user to relay it.

### Codex using the response

While a request is `OPEN`, check the Doc at natural synthesis points rather than
busy-polling. When the matching `Response to Request N` appears, immediately set
`Status: APPLYING` before doing substantive work from it.

`APPLYING` means that response has already been consumed. Continue the current
incorporation from the repository state and `PROGRESS.md`; consult the response
again only for needed details, and do not restart, re-answer, or present it as a
new handoff. After addressing the material findings and recording any durable
unresolved issue, set the request to `CLOSED` or supersede it, push, and
continue. If the status is `CLOSED`, ignore old responses in the review Doc.

There are no handoff ZIPs, response-import files, random tokens, response
hashes, round directories, transport tests, bridge checkers, or manual ferrying.
A separate Drive folder is unnecessary. If an auxiliary Drive document, table,
or figure genuinely helps, link it from the review Doc; durable proof material
normally belongs in GitHub.

If access is missing, identify the exact permission, leave the request intact,
and continue work that does not depend on the channel. Do not silently revert
to manual ferrying.

## 9. Continuity and rotation

At startup or resume, reconstruct the target, requested deliverables, current
focus, mathematical picture, and best next action from `PROBLEM.md` and
`PROGRESS.md`. Read `BRIDGE.md` and `PRO_REQUEST.md` when communication is active.
Read `lean/AGENTS.md` when the current work is materially in `lean/`.

After compaction, reread the canonical files needed for reliable reasoning. Do
not answer an older user message again merely because it remains visible. A
question is consumed once it has been answered or acted on unless the user
explicitly reopens it. For Pro work, `OPEN` means await the matching response,
`APPLYING` means continue an incorporation already underway, and `CLOSED` means
do not act on old review material. Compaction alone is not a reason to run
generic checks, stop, or rotate.

If Codex repeatedly re-answers an old user question or restarts the same Pro
response, treat that as a continuity failure: save the durable mathematical
state, push, and recommend rotation.

At natural synthesis points, silently assess whether the current chat can still
reconstruct the project coherently. If a fresh Codex chat would materially
reduce context-loss risk:

1. update `PROGRESS.md` with the durable mathematical and focus state;
2. save, commit, and push proof-bearing work;
3. begin the next user-facing message with `CODEX ROTATION RECOMMENDED` and one
   short reason; and
4. avoid beginning a major new branch that should start in the fresh chat.

If rotation is unnecessary, say nothing about chat health. A replacement Codex
or Pro reads the same repository and review Doc; no proof content is moved by
hand.
