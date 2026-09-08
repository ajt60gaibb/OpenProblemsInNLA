# Math-First Proof and Lean Project — Codex ↔ Pro

This template supports two kinds of work in one private GitHub repository:

```text
proof/   human-readable mathematics, TeX, notes, and computer-assisted proof
lean/    Lean statement, proof, certified computation, and optional final audit
```

The mathematical target, progress record, and Codex–Pro bridge are shared at
repository root. The active Goal prompt decides whether Codex concentrates on
the mathematical proof, the Lean development, or both. There is no mode switch
to configure and no need to create a second repository.

```text
Codex develops and pushes GitHub
                 ↓
Pro reads GitHub and writes one Google review Doc
                 ↓
Codex reads the Doc, acts on the mathematics, and continues
```

The user never copies proof text, Lean code, reviews, certificates, or evidence
between the agents.

## Repository layout

- `PROBLEM.md` — canonical mathematical target and required deliverables.
- `PROGRESS.md` — current mathematical state and current work focus.
- `PRO_REQUEST.md` — the one open request, if any, for independent Pro review.
- `BRIDGE.md` — link to the shared Google review Doc.
- `AGENTS.md` — standing proof-first rules for Codex and Pro.
- `proof/` — flexible workspace for TeX, proof notes, CAP code, exact data, and
  proof-bearing certificates.
- `lean/` — Lean project and Lean-specific instructions.
- `.codex/` — context-restoration, rotation, and the narrow individual-artifact
  hash policy.

`proof/` and `lean/` are sibling workspaces, not competing projects. Lean can
expose an error in the mathematical proof; informal or computer-assisted work
can supply the structure or exact artifacts needed by Lean.

# One-time account setup

## 1. Make this repository a GitHub template

In the master repository's GitHub settings, enable **Template repository**.
Create future projects with **Use this template**, so each project starts with a
clean history and no earlier theorem state.

## 2. Connect GitHub to ChatGPT Pro

In ChatGPT, open **Settings → Apps/Plugins → GitHub**, connect the desired
account, and grant access to the private repositories Pro may review.

For the fewest future steps, keep proof projects in a dedicated GitHub account
or organization and grant the ChatGPT GitHub app access to all repositories
there. For least privilege, authorize each new repository separately.

The ordinary ChatGPT GitHub connection is intentionally read-only: Pro reviews
the repository, while Codex owns all commits and pushes.

## 3. Connect Google Drive

In ChatGPT, open **Settings → Apps/Plugins → Google Drive** and connect the
account that will hold review Docs. Enable the available actions for creating,
reading, and updating native Google Docs. A managed workspace may require an
administrator to enable write actions.

The same account connection is reused across projects. No Drive folder is
required.

# Start a project

## 1. Create and open the repository

Choose **Use this template → Create a new repository**, make it private, and
open it in Codex. If GitHub access is repository-specific, authorize this new
repository for ChatGPT Pro.

In Codex, select Google Drive under **Sources → Use plugins**. Review and trust
the repository's small `.codex` hooks when prompted.

## 2. State the objective once

Send a natural Goal prompt. Codex infers the focus from what you ask.

### Develop the mathematical theorem or CAP

```text
/goal Resolve the mathematical problem below autonomously. Develop the rigorous
mathematical proof, TeX exposition, and any genuinely necessary
computer-assisted proof in proof/. Follow AGENTS.md.

[PASTE THE PROBLEM]
```

### Develop the Lean formalization

```text
/goal Formalize and prove in Lean the theorem described below and in the
repository. Work primarily in lean/, using proof/ and PROBLEM.md as the
mathematical source. Follow AGENTS.md and lean/AGENTS.md.

[PASTE THE THEOREM OR IDENTIFY THE SOURCE FILES]
```

### Develop both together

```text
/goal Resolve the mathematical problem below and produce both a rigorous proof
in proof/ and a Lean formalization in lean/. Use each track to check and improve
the other. Follow AGENTS.md.

[PASTE THE PROBLEM]
```

These examples are conveniences, not special syntax. Plain language such as
“now focus on formalizing the established theorem in Lean” is enough.

On the first Goal, Codex automatically:

1. replaces the untouched `PROBLEM.md` template with the exact target and
   requested deliverables;
2. initializes `PROGRESS.md`, including the current focus;
3. preserves and reads any useful files already present in `proof/` or `lean/`;
4. commits and pushes the initialized project; and
5. begins the requested mathematical work immediately.

The user does not edit setup files, create a project generator, or initialize a
Lean project by hand.

# Switch focus later

Use the same repository. Send a new Goal that states the new objective, for
example:

```text
/goal The mathematical proof in proof/ is now the source. Formalize its main
theorem in lean/, repair any genuine source defect you discover, and continue
until the requested Lean completion criterion is met.
```

Codex updates the deliverable scope and current focus because the user has
explicitly changed or expanded the Goal. No files or reviews are moved between
projects.

The focus is a priority, not a wall. In proof-focused work, Codex may use Lean
when it materially helps. In Lean-focused work, it may repair or clarify the
mathematical source when formalization exposes a real issue. It should not do
substantial work in the inactive track merely because the folder exists.

# Lean development levels

The `lean/` folder supports both ordinary proof development and a higher-
assurance final audit.

For an ordinary Lean proof, the essential work is:

1. state the intended theorem faithfully in `lean/Challenge.lean` and shared
   definitions;
2. prove the same declaration independently in `lean/Solution.lean` and helper
   modules; and
3. make the relevant Lean build succeed with no proof-side `sorry` or `admit`.

The statement audit, numerical-target record, independent review guide,
Comparator configuration, and `formalization.yaml` are available when source
fidelity or publication-grade verification requires them. They are not a
reason to delay exploratory mathematics or to run a fixed ceremony on every
Lean task. The exact Goal and completion criterion determine how much final
verification is required.

Do not run Lean setup or verification merely because the folder is present. A
proof-focused Goal may leave `lean/` untouched.

# Codex–Pro review loop

1. Codex works in the relevant workspace and pushes meaningful mathematical
   checkpoints.
2. When independent review would add real value, Codex opens and pushes
   `PRO_REQUEST.md`, identifying the focus as `PROOF`, `LEAN`, or `JOINT`.
3. On the first review only, Codex creates the native Google review Doc, records
   its URL in `BRIDGE.md`, and pushes the link.
4. Codex prints a complete wake message such as:

```text
@GitHub @Google Drive Review the open PRO_REQUEST.md in OWNER/REPOSITORY as the
independent Pro mathematical referee. Follow AGENTS.md, BRIDGE.md, and any
workspace-specific AGENTS.md named in the request. Write the substantive
response to the linked Google Doc.
```

5. The user sends that one message to the persistent Pro chat.
6. Pro reads the private repository and appends its review to the linked Doc.
7. Before using that response, Codex changes the request from `OPEN` to
   `APPLYING`. It then addresses the mathematics, changes it to `CLOSED`, pushes,
   and continues the same Goal. This prevents an old response from being handled
   again after compaction or resume.

One wake message per review is the only recurring user action. There are no
handoff ZIPs, copied reviews, response-import files, random tokens, round
directories, transport tests, or communication validators.

# Existing projects

A new repository may already contain a manuscript, proof, code, exact data, CAP
certificates, or Lean files. Place mathematical and CAP material under `proof/`
and Lean material under `lean/`, then state the objective in the Goal prompt.
Codex should preserve useful work and initialize the root project record from
what actually exists.

# Rotation

When Codex says `CODEX ROTATION RECOMMENDED`, let it finish its push, open a
fresh Codex chat in the same repository, enable Google Drive, and send:

```text
/goal Continue the current objective in PROBLEM.md under AGENTS.md. Reconstruct
the durable state from PROGRESS.md and BRIDGE.md and continue autonomously in
the current focus.
```

When Pro says `PRO ROTATION RECOMMENDED`, open a fresh Pro chat and send Codex's
current one-line wake message. No mathematical content is transferred by hand.

# Troubleshooting

**Pro cannot see the private repository.** Confirm that the exact repository is
authorized under ChatGPT's GitHub app settings. Newly authorized repositories
may take a short time to appear.

**Codex cannot create the first review Doc.** Confirm that Google Drive is
selected for the Codex task and has Doc-creation permission. Only as a fallback,
create one blank native Google Doc and give Codex its URL once.

**Pro cannot update the Doc.** Confirm that the connected Google account can
edit it and that Google Drive write actions are enabled.

**Codex cannot read the response.** Confirm that Google Drive is selected and
that `BRIDGE.md` contains the correct Doc URL.

Do not work around a connection issue by copying substantive proof material
between chats. Leave the request intact, fix the permission, and resume.
