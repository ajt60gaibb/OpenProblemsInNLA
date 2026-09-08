# Pro–Codex Bridge

Google review Doc: `AUTO-CREATE_WHEN_FIRST_PRO_REVIEW_IS_OPENED`

## First review

Do not create communication infrastructure during ordinary project
initialization. When Codex opens the first Pro review and the placeholder above
is still present, use the connected Google Drive plugin to create one native
Google Doc named:

```text
Pro Reviews — OWNER/REPOSITORY
```

Begin the Doc with:

```text
# Pro Reviews — OWNER/REPOSITORY

Codex places the current proof, Lean, or joint review request in PRO_REQUEST.md.
Pro appends substantive responses here.
```

Replace the placeholder with the Doc URL and push this file with the open
`PRO_REQUEST.md`. Ask the user to create a blank native Google Doc only if the
Google Drive create action or permission is genuinely unavailable.

## Roles

- Codex writes and pushes GitHub and reads the review Doc.
- Pro reads GitHub and appends reviews to the review Doc.
- The same Doc serves `PROOF`, `LEAN`, and `JOINT` requests.
- The user only wakes Pro with the exact message printed by Codex.

A separate Drive folder is unnecessary. If an auxiliary Drive file later has
genuine mathematical value, link it from the review Doc. Durable proof and Lean
material normally belongs in GitHub.
