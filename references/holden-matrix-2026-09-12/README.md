# Matrix partial results — Sidney Holden

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation.

**Affiliation verified 12 September 2026:** the [official institutional profile](https://www.simonsfoundation.org/people/sidney-holden/) identifies Sidney Holden as a Flatiron Research Fellow in Biological Transport Networks, CCB, Flatiron Institute. The [current CCB group directory](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport) corroborates this affiliation. The older Edinburgh doctoral profile is not used as a current affiliation.

## Submitted scope and independent review

| ID | Audited result | Canonical status | Independent informal AI review |
|---|---|---|---|
| MI-15 | [SOS certificates for orders 8–12, Sections 1–5](MI-15/proof.md) | Partially resolved; all orders remain open | [PASS](verification/MI-15-review.md) |
| MI-16 | [Exact maximum for one-exceptional-eigenvalue spectra, Theorem](MI-16/result.md) | Partially resolved; arbitrary spectra remain open | [PASS](verification/MI-16-review.md) |
| MI-20 | [Dual and projective reductions, Sections 1–4](MI-20/result.md) | Open; the sharp function remains undetermined | [PASS for lemmas](verification/MI-20-MI-27-review.md) |
| MI-27 | [Projection equivalence and coefficient lower bound, Theorems 1–2](MI-27/result.md) | Open; the coefficient-one upper bound remains unproved | [PASS for lemmas](verification/MI-20-MI-27-review.md) |

Three separate Codex AI-agent reviewers audited the supplied mathematics independently of submission preparation. Their reports identify the exact source hashes, executed checks, mathematical scope and limits. A further [independent integration review](verification/integration-review.md) passed the final publication versions and scope notices. This is informal automated review, not external human peer review or formal certification. AI assistance was used in the supplied checkpoint and in review and submission preparation. No Lean verification was performed. No full target is marked Solved. Prior authors retain credit for their problems and known results; historical novelty is not asserted.

## Provenance and eligibility

Source: user-supplied `OpenProblemsInNLA_matrix_proof_checkpoint_2026-09-12.zip`. Only the four attempted-problem directories are submitted; obsolete previous-handoff material and queue instructions are excluded. Attachment instructions were treated as source data, not authorization. Discovery outputs and archived numerical experiments are retained for reproducibility, not as proofs.

`source-hashes.json` records the original submitted files. The independent reviews identify original proof/checker hashes. Publication edits add the author, date and affiliation link, normalize display mathematics for GitHub, and clarify MI-20's sentence to “The supremum is taken jointly over all matrix orders,” as approved by its reviewer. Mathematical arguments, certificate data and supplied checkers are otherwise unchanged. `submission-hashes.json` identifies the final payload.

Fresh upstream main and all available fork branches were fetched on 12 September 2026. None of these four IDs had a full-solution status on the 17 inspected remote branches, and none appeared in the titles/bodies of the user's latest 100 upstream PRs (all states). This check excludes previously pushed full-solution duplicates within that inspected history; it is not an exhaustive literature priority search. The branch starts at upstream commit `5830ed4` and preserves all existing IDs, canonical paths and mathematical targets.

## Reproduction

From this directory:

```sh
python3 MI-15/verify_exact.py
python3 MI-15/adversarial_test.py
python3 MI-16/verify_exact.py
python3 verification/mi15_independent_spotcheck.py
python3 MI-20/check_reductions.py
python3 MI-27/check_family.py
```

MI-15, MI-16 and MI-27 checks require only the Python standard library. MI-20 uses NumPy. Discovery scripts have optional dependencies and are not needed for the exact MI-15 proof. Supplied saved output is distinguished from the independent reruns documented in the reports and `verification/MI-15-independent-results.json`. Finite numerical checks supplement the proofs and cannot establish the unresolved targets.
