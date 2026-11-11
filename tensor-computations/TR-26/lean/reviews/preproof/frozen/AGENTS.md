# Permanent problem numbering

The maintainer requires every published problem number to remain unchanged forever.
Never renumber, compact, recycle, or reassign an existing ID, including after a
solution, withdrawal, or category-listing change. Preserve its canonical README
path and original mathematical target. Keep solved or withdrawn entries as
retained pages; changing the open-problem count does not change any ID.

`problem_ids.json` is the append-only ID-to-canonical-README registry. For a new
entry, choose the next number above every registered number with that prefix
(for example, `RA-18` after `RA-17`), and explicitly add its ID/path pair to the
JSON object. Never fill gaps. Use at least two digits (`RA-01`, `RA-100`).

Before regenerating indexes, validate against the branch's published base:

```bash
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
```

The validator also runs automatically before index generation and in CI. It
checks identity and paths; review still must ensure an existing page's target
has not been replaced by an unrelated problem. Do not weaken the safeguards to
make a numbering change pass.
