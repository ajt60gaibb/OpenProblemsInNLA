# Sources and provenance

Prepared for the MI-27 request in this conversation, dated 12 September 2026.

## Target

Public problem page:
https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/matrix-inequalities-and-norms/MI-27

Plain-text statement read through the web:
https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/matrix-inequalities-and-norms/MI-27/README.md

The observed page labels the problem “Constant one in the logarithmic commutator inequality,” marks its status Open, and lists its last check as 2026-09-10. The theorem proved here addresses its full positive-definite, all-dimensions statement and full trace-norm convention. A website status label is not taken to establish historical priority of this proof.

## Uploaded findings

The provided archive was mounted at:
`/mnt/data/5f147040-2e2d-4036-9951-fe13d9de3d8b.zip`

Archive SHA-256:
`4e4f940a35cdd825749cd689a325fae068a6ed07b84cd7c9996593bedd64995d`

The relevant original member was:
`OpenProblemsInNLA_matrix_proof_checkpoint_2026-09-12/MI-27/result.md`

Original member SHA-256:
`4aaf931209d07a194761ff2fb2867923462503bb390c4185f445aa390a5972c7`

An unchanged copy is included as `provenance/input_MI27_result.md`.
The supplied pack proves the projection equivalence and the strictly positive definite 2-by-2 sharpness family. It explicitly leaves the coefficient-one upper bound unproved. Those two findings are attributed to the pack and are reverified in the present text. The upper-bound proof instead uses the positive-part unitary Lipschitz lemma and the published relative-entropy representation.

The pack records README blob `d7d202d2c9b313d426569547c5466e059a430c0e`; this is a provenance observation from the pack, not a newly verified repository commit identifier.

## Essential published input

Péter E. Frenkel, *Integral formula for quantum relative entropy implies data processing inequality*, Quantum 7, 1102 (2023).
DOI: 10.22331/q-2023-09-07-1102.
https://arxiv.org/abs/2208.12194
Version used: arXiv:2208.12194v4, revised 5 September 2023.
Exact location: Theorem 6, PDF pages 6–7.

Christoph Hirche and Marco Tomamichel, *Quantum Rényi and f-divergences from integral representations*, Communications in Mathematical Physics 405, 208 (2024).
DOI: 10.1007/s00220-024-05087-3.
https://arxiv.org/abs/2306.12343
Version used: arXiv:2306.12343v3, revised 26 August 2024.
Exact location: Corollary 2.3, equation (2.22), PDF page 7.
The theorem was read in HTML and its equation visually verified in the PDF. Section 2.7, Proposition 2.9, also treats the skew-divergence transformations; the needed substitutions are derived explicitly in the present proof.

No full external research paper is bundled. The package contains citations and the mathematical formulas used, with an original derivation of the MI-27 consequence.

## Access and authorship scope

The public site and research papers were read through web tools, without the GitHub connector. No remote repository or external account was modified. The proof write-up and verification code were produced by the assistant during this conversation. The stated proof is analytic; it is not an external referee certification or proof-assistant formalization. No historical publication-priority claim is made.


## Repository submission record (12 September 2026)

Author: **Sidney Holden**, as explicitly requested by the submitter. Current affiliation:
**Center for Computational Biology, Flatiron Institute, Simons Foundation**.
Verified on 12 September 2026 against the [official institutional profile](https://www.simonsfoundation.org/people/sidney-holden/), which identifies Sidney Holden as a Flatiron Research Fellow in Biological Transport Networks at CCB.
The institution's [CCB staff directory](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport&type=ccb-staff) independently lists this role. The earlier Edinburgh profile is historical and was not used as current affiliation.

The above preparation narrative describes the uploaded artifact's earlier creation.
Its disclosure of assistant-produced proof text and code is retained; author attribution
here does not assert that the text was written without AI assistance.
This submission adds author/affiliation front matter, rebuilds the PDF, and appends a
separate independent Codex AI-agent audit. The mathematical proof is unchanged.
The original ZIP is identified by SHA-256: `f9dcb5b3057bf279f6f87ee5a6a71e1a841a1c29140f6a3efef0396caf22991f`.
Original file hashes are retained in `provenance/original-SHA256SUMS.txt`; all were checked before editing.
`SHA256SUMS.txt` records the final submitted files.

Duplicate screening inspected current upstream main, fetched fork branches and upstream
PR history. [PR #186](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/186)
contains only the projection reduction and sharpness family and explicitly leaves the
universal upper bound open. It is related prior work, not a duplicate full solution.
The present submission preserves that credit and submits the complete upper bound in a new PR.
No Lean verification is performed, as requested. Independent AI review is informal,
not external human peer review, and no historical-priority claim is made.
