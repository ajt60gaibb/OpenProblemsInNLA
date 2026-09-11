# GitHub upload notes

The ZIP contains one top-level directory, `OpenProblemsInNLA_recovered`. Extract it first. Its contents can be used as a standalone review repository or placed in a clearly named contribution directory on a branch of an existing repository.

Start with `README.md`, `Research_manuscript.pdf`, `STATUS.md`, and the verification scripts. Include the rest of the files so the mathematical sources, corrected certificates, source register, and review limitations remain attached to the results. The archive does not contain an upstream patch because the current checkout and contribution conventions could not be retrieved.

For a standalone local repository, these commands initialize and commit the extracted material; they do not publish or push it:

```bash
cd OpenProblemsInNLA_recovered
python3 scripts/check_integrity.py
python3 verification/run_all.py
python3 verification/rook_partial.py
git init
git add .
git commit -m "Add recovered NLA proof drafts and exact certificates"
```

Rerunning checks changes timestamped outputs, so a subsequent integrity check against the packaged manifest will report those expected changes. Keep the original ZIP as the immutable reconstruction snapshot, or regenerate the manifest with `python3 scripts/create_manifest.py` after intentional edits.

For an upstream contribution, first verify the actual problem filenames and submission policy. The IE labels here are provisional. The notes in `submission-drafts/` describe the proposed mathematical contribution without pretending that an upstream change has already been accepted. Keep the AI-assistance and scope disclosures. Do not mark the entire problem section solved or describe the partial rook example as a sharp theorem.

No remote URL, branch, account, author identity, or external publication action has been chosen on the submitter's behalf.
