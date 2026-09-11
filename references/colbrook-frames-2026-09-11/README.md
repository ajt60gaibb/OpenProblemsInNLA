# Reviewed frame and sampling submissions - 11 September 2026

**Author: Matthew J. Colbrook**  
Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom.  
Email: m.colbrook@damtp.cam.ac.uk. Affiliation checked against the [official university homepage](https://www.damtp.cam.ac.uk/user/mjc249/home.html) on 11 September 2026.

Submitted by the author as `frames_submission_all.zip`. The [archive manifest](bundle-sha256.json) records the original archive and file hashes. Authorship is recorded at the author's request; no priority or historical novelty determination is made. Independent Codex agents reviewed the complete mathematical manuscripts and certificate mechanism. This is independent agent review, not external human peer review or formal proof-assistant certification.

| Catalog entry | Result and primary locator | Review | Catalog status |
| --- | --- | --- | --- |
| [FR-02](../../frames-and-matrix-designs/FR-02/README.md) | [Sampling manuscript](manuscripts/sampling_thresholds.pdf), Theorem 2: full and nearly-full cyclic Fourier regimes | [Sampling review](verification/reviews/sampling-review.md) | Partially resolved |
| [FR-04](../../frames-and-matrix-designs/FR-04/README.md) | [Planar manuscript](manuscripts/planar_projection_bound.pdf), Theorems 1 and 3: weighted planar and polynomial subframe bounds | [FR-04 review](verification/reviews/FR-04-review.md) | Open; exponential target is not established |
| [FR-09](../../frames-and-matrix-designs/FR-09/README.md) | [Certificate proof](conference-proof.md), Sections 1-4: dimensions 166, 209, 256, 1505 only | [FR-09 review](verification/reviews/FR-09-review.md) | Partially resolved |
| [FR-10](../../frames-and-matrix-designs/FR-10/README.md) | [Sampling manuscript](manuscripts/sampling_thresholds.pdf), Theorems 1-2: Walsh sparsities 1-4 and full/nearly-full regimes | [Sampling review](verification/reviews/sampling-review.md) | Partially resolved |
| [FR-11](../../frames-and-matrix-designs/FR-11/README.md) | [Twelve-measurement manuscript](manuscripts/twelve_measurements.pdf), Theorem 1 and subsequent stability/decoding results: real dimension seven upper bound | [FR-11 review](verification/reviews/FR-11-review.md) | Partially resolved |

No complete catalog problem is marked Solved by this batch. All five original targets and ratings are preserved. In particular, twelve measurements is an upper bound rather than a minimum, the sampling results do not cover all sparsities, and four certified ETF dimensions do not establish all-dimension existence. The polynomial phase-retrieval order was already known.

## Provenance and changes

The three complete submitted TeX sources are retained unchanged in `submitted/`. The generated files in `manuscripts/` add the requested author, verified affiliation, date, explicit scope and review links. The mathematical body after the title is unchanged; full-source hashes in the reviews gate generation through [the rendering manifest](manuscripts.json) and `tools/render_reviewed_tex.py`.

All original scripts are preserved in `verification/submitted-code/`. Working copies are in `verification/`; the decoder has a documented correction to prevent norm overflow/underflow on representable finite data. Its exact-arithmetic theorem is unaffected. The source archive's floating-point diagnostic reports are retained in `verification/submitted-reports/` and are distinguished from fresh reruns. The conference proof is an agent-prepared exposition of the author's supplied construction and certificate method.

Only four conference certificate files were supplied. They are stored once in `verification/certificates/`. The original catalog report lists dimensions 166-256, but the 88 dimensions other than 166, 209 and 256 have no certificates in this archive and are not independently certified here. No claim of rigorous verification of that whole range is made.

## Reproduction

Run from the repository root with Python 3, NumPy, SymPy and SciPy. The conference verifier can use only the standard library with `--pure-python`; the fast backend uses NumPy integer products with a proved no-overflow guard and an exact coarse-grid error bound. Search/generation scripts are exploratory and are not proof certificates.

```sh
python references/colbrook-frames-2026-09-11/verification/verify_r7.py --out references/colbrook-frames-2026-09-11/verification/r7-rerun --angles 0 --restarts 0 --seed 3
python references/colbrook-frames-2026-09-11/verification/verify_sampling.py --seed 1 --out references/colbrook-frames-2026-09-11/verification/sampling-rerun.json
python references/colbrook-frames-2026-09-11/verification/decode_r7.py --self-test --seed 1 --count 300 --out references/colbrook-frames-2026-09-11/verification/decoder-rerun.json
python references/colbrook-frames-2026-09-11/verification/verify_conference.py references/colbrook-frames-2026-09-11/verification/certificates/conference_certificate_d166.json references/colbrook-frames-2026-09-11/verification/certificates/conference_certificate_d209.json references/colbrook-frames-2026-09-11/verification/certificates/conference_certificate_d256.json references/colbrook-frames-2026-09-11/verification/certificates/conference_certificate_d1505.json --out references/colbrook-frames-2026-09-11/verification/conference-rerun.json
python tools/render_reviewed_tex.py references/colbrook-frames-2026-09-11/manuscripts.json
python tools/update_catalog.py
python tools/render_problems.py FR-02 FR-04 FR-09 FR-10 FR-11
```

The fresh [conference report](verification/conference-rerun.json) passes all four exact rational contraction tests. A separate [pure-Python dimension-166 check](verification/conference-d166-independent-pure-python.json) and [independent small-dimension Fraction model check](verification/conference-independent-model-check.py) audit the integer product and Jacobian implementations. The [sampling rerun](verification/sampling-rerun.json) and [exact twelve-matrix rerun](verification/r7-rerun/r7_integer_verification_seed3.json) pass. Finite numerical tests supplement the analytic reviews; they do not prove asymptotic or all-input claims.
