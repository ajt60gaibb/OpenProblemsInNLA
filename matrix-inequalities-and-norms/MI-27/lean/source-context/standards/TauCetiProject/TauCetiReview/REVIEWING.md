# Reviewing a PR yourself

Tau Ceti has a CI path that reviews with the metered Anthropic and OpenAI **APIs**, but production
review generation is currently disabled there to conserve that budget. Reviews instead come from
the trusted operator-run worker and from ad hoc command-line runs. `tauceti-review` lets a trusted
person run the same review on their **own Claude / Codex / Kiro subscription**: the inference runs
through the locally logged-in provider CLI, so there is no per-token bill. It is the same engine,
same rubrics, same scoreboard and per-rubric threads — only the inference auth and who posts change.

This is for people the project already trusts (maintainers, regular contributors). The tool is
read-only and posts under *your* GitHub identity, but nothing stops a reviewer from rubber-stamping
— the safeguard is social, not technical. See [SECURITY.md](SECURITY.md) for the threat model the
CI harness defends and which parts a local run deliberately drops.

## Prerequisites

On your `PATH`, all logged in:

- `git`
- [`gh`](https://cli.github.com/) — run `gh auth login` (this identity posts the review and reads
  the PR).
- `claude` ([Claude Code](https://www.npmjs.com/package/@anthropic-ai/claude-code)) signed into a
  Claude subscription, and/or `codex` ([Codex](https://www.npmjs.com/package/@openai/codex)) signed
  into a ChatGPT subscription. You need **at least one**; each rubric is judged by whichever you
  have. With both, the reviewer is drawn per rubric, like CI.
- For explicit Kiro reviews, `kiro-cli` signed in with `kiro-cli login` (or a
  headless `KIRO_API_KEY`). Kiro is never auto-drawn.
- Python ≥ 3.10.

## Install

With [uv](https://docs.astral.sh/uv/):

```bash
# one-off, no install:
uvx --from git+https://github.com/TauCetiProject/TauCetiReview tauceti-review 42

# or install the command:
uv tool install git+https://github.com/TauCetiProject/TauCetiReview
tauceti-review 42
```

Or from a checkout (also how to hack on it):

```bash
git clone https://github.com/TauCetiProject/TauCetiReview
cd TauCetiReview
uv run tauceti-review 42          # or: pipx install . / pip install .
```

The rubrics and the review engine always come from a TauCetiReview checkout — the one you ran from
if it is one, otherwise a cached shallow clone under `~/.cache/tauceti-review` that refreshes each
run — so the rubrics never drift from the engine.

## Use

```bash
tauceti-review 42                       # review PR #42, PRINT the verdicts — posts nothing
tauceti-review 42 --post                # also post the scoreboard + threads, as you
tauceti-review 42 --rubrics scope,correctness,reuse
tauceti-review 42 --reviewer claude     # use only Claude even if both are installed
tauceti-review 42 --reviewer kiro --kiro-model gpt-5.6-sol
tauceti-review 42 --reviewer kiro --kiro-model claude-opus-5
tauceti-review 42 --reviewer deepseek   # use DeepSeek via OpenRouter + the `pi` agent
tauceti-review 42 --no-mathlib          # skip the Mathlib clone (faster; weaker reuse checks)
```

It **defaults to a dry run**: it prints the scoreboard and each rubric's thread and posts nothing.
Add `--post` to publish. Useful flags:

| flag | effect |
|---|---|
| `--post` | post the scoreboard comment + per-rubric review threads to the PR, under your GitHub login |
| `--rubrics a,b,c` | review only these rubrics (default: all of them) |
| `--reviewer claude\|codex\|kiro\|sonnet\|deepseek\|minimax\|grok` | restrict to these reviewers (default: every auto-drawn one you have — `claude` and `codex`). Direct `claude` is pinned to exact `claude-opus-5`. `kiro` is explicit-only and always uses the exact `--kiro-model`. `sonnet` is the `claude` CLI pinned to Sonnet. `deepseek`/`minimax`/`grok` run an OpenRouter model through the [`pi`](https://github.com/badlogic/pi-mono) agent and need `pi` on PATH + `OPENROUTER_API_KEY`. All but `claude`/`codex` are explicit-only (never auto-drawn) |
| `--kiro-model MODEL` | exact Kiro model ID; defaults to `gpt-5.6-sol`. Use `claude-opus-5` for Kiro's current Opus |
| `--mode commit` | review only rubrics not already passing in the local store (default `manual` = all) |
| `--no-mathlib` | skip fetching pinned Mathlib source; `reuse`/`naming` can't grep Mathlib |
| `--repo owner/name` | review a different repo (default `TauCetiProject/TauCeti`) |
| `--auth api` | use the matching `ANTHROPIC_API_KEY`, `OPENAI_API_KEY`, or `KIRO_API_KEY` instead of a browser login |
| `--keep` | keep the temporary workspace for inspection |

## What it does

1. Reads the PR head SHA, diff, and description via `gh`.
2. Builds the same read-only reviewer workspace CI uses: the PR source at its head, the roadmap
   repo, and (unless `--no-mathlib`) the pinned Mathlib source for `reuse`/`naming` to grep.
3. Runs each rubric through `claude -p`, `codex exec`, exact-model `kiro-cli chat`, or the `pi`
   agent against OpenRouter, **read-only** (`Read`/`Grep`/`Glob`, or pi's `read`/`grep`/`ls` —
   no shell, no writes). In `--auth subscription` mode Claude, Codex, and Kiro use the logged-in
   subscription; the OpenRouter reviewers are pay-per-token and use
   `OPENROUTER_API_KEY`. Each reviewer runs in a **clean room**: a throwaway HOME seeded with only
   its own credential, so it ignores your personal `CLAUDE.md` / `AGENTS.md`, skills, plugins, and
   settings (and those are disabled outright). The review depends on the rubrics and the PR, not
   on who runs it.
4. Reads each verdict from a fresh one-time marker token, so nothing in the PR text can forge an
   `approve` (this anti-forgery channel is kept even though you are trusted).
5. Prints the scoreboard + threads, and with `--post`, publishes them via `gh` as you.

The posted scoreboard is the live verdict consumed by auto-merge: both merge paths read the newest
marked scoreboard and require it to name the current head. The engine also writes detailed records
for the TauCetiData analytics/provenance archive, but archive publication is not part of the merge
gate and a contributor needs no TauCetiData write access for a posted review to count.

## Notes

- **Cost line.** For Claude/Codex, the scoreboard's `Review spend: $X` is a *notional*
  API-equivalent estimate from token usage. Kiro 2.x exposes no per-turn token telemetry, so Kiro
  subscription runs are recorded at $0 rather than assigned a fictional API price.
- **Who it posts as.** With `--post`, comments are created under your `gh` identity, not the review
  bot's, and as a fresh scoreboard comment (a local run keeps no state shared with CI, so it won't
  edit the bot's comment in place). The authenticated login is also recorded as `submitted_by` in
  the scoreboard's hidden provenance so cooperating workers can give that reviewer first refusal on
  the next head.
- **Subscription terms.** Driving a personal Claude/ChatGPT/Kiro subscription as an automated reviewer
  is fine for occasional, interactive, human-initiated runs like this. Standing it up as a 24/7
  self-hosted auto-reviewer is closer to API-tier usage and likely outside subscription terms — for
  always-on review, enable Tau Ceti's CI path and use `--auth api` with API keys.
- **Reproducibility.** The clean room means your personal `~/.claude/CLAUDE.md`, `~/.codex/`
  config/`AGENTS.md`, skills, and MCP servers do **not** influence the review — two people running
  the same rubrics on the same PR get reviews that differ only by the model, not by their local
  setup. (The repo's own in-tree `CLAUDE.md` is still visible, as part of the code under review.)
  On macOS, where the login lives in the keychain rather than a credential file, it falls back to
  your real HOME and prints a note; pass `--auth api` with a key for a guaranteed clean room there.
- **Determinism.** With both CLIs installed the reviewer is random per rubric, so two runs can
  differ on borderline rubrics — the same property the CI review has.
- **Concurrent reviewers.** Before spending inference, a contributing run (one that posts or
  archives) posts a short-lived `review in progress` comment scoped to the `head` alone and checks
  for one already there. If another reviewer already holds the commit, this run skips it entirely —
  so a commit is reviewed once regardless of model, and a fleet never pays twice. A *different* model
  is not a distinct unit (the first claimer wins); only a new push, being a fresh head, is a fresh
  unit. Simultaneous claimers wait five seconds for GitHub's comment replicas to settle, then the
  lowest comment id wins. The marker self-expires (a crashed reviewer never blocks anyone) and is
  deleted when done.
  It needs only the ability to comment, so an independent reviewer with no repo write still
  coordinates. Pass `--no-coordinate` for a private read-only pass that touches the PR not at all
  (at the cost of possible duplicate spend); a `--shadow` arm opts out automatically.

## Shadow reviews (A/B arms)

A shadow review runs the same PR through alternative rubrics and/or models, archives the
results to [TauCetiData](https://github.com/TauCetiProject/TauCetiData), and posts **nothing**
— the PR thread and the production review state are untouched. This is how review variants are
evaluated against each other before being adopted.

    tauceti-review 139 --shadow --label deepseek-arm --reviewer deepseek
    tauceti-review 139 --shadow --label rubrics-v2 --rubrics-sha <TauCetiReview commit>

`--rubrics-sha` pins the rubrics *and* the engine to that commit (a cached per-SHA checkout),
so an arm reruns exactly the code that existed then. Arms always run every requested rubric
fresh (`--mode manual` semantics, scratch store, no carried-forward case files) so that two
arms over the same `(PR, head, rubric)` are comparable; records land with `arm: shadow:<label>`
and pair up with the production run in TauCetiData's `ab_pairs` view. In CI, the
`shadow-review` workflow (manual dispatch) does the same with API keys and a per-run budget.
