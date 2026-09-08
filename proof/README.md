# Mathematical proof workspace

Use this folder for the human-readable mathematical development:

- TeX manuscripts and bibliographies;
- proof notes, derivations, examples, and counterexamples;
- computer-assisted proof code;
- exact input data, witnesses, and proof-bearing certificates;
- concise source notes needed to identify the theorem and conventions.

Let the mathematics determine the internal layout. Do not create a hierarchy of
empty folders, wrappers, tests, or reports merely because this is a template.
Create only the files and subdirectories the actual proof needs.

`PROBLEM.md` at repository root is the canonical target. Material here is the
source used by the Lean formalization when one is requested. If Lean exposes a
genuine error or ambiguity, repair the source deliberately and record the
change in `PROGRESS.md`; do not let the two tracks silently diverge.

This placeholder may be replaced or removed once real project material makes it
unnecessary.
