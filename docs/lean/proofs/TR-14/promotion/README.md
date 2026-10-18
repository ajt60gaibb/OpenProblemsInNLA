# TR-14 verification notice and status promotion

The exact proof-commit Linux workflow succeeded, and two independent strict
replays passed 41/41 controls before this promotion. The new marked notice
changes status to Lean verified and dates the verification. All original text,
mathematical targets, authorship credit, IDs and canonical paths are preserved.
Five exact original files remain archived in `../originals-main-36767/`.

The repository renderer succeeded without warnings on its first attempt.
`render-attempt-1.log` and `render.log` are exact output; `pdfinfo.txt`, both page
images and both independent visual reports retain the layout evidence.
`preservation.json` checks the intentional promotion separately from the earlier
strict 828-file byte-preservation record. The independent failed first attempt
is retained: its only failure was a status-line classifier that did not allow
original Markdown hard-break spaces. The corrected classifier still requires
the exact anchored status and preserves every other guard.

All 82 checked Lean proof/statement inputs remain unchanged. The older exact
proof-commit receipt retains its original 139-input hashes. Later descriptive
and status changes require a fresh committed-package Linux receipt and are not
silently attributed to the older artifact.
