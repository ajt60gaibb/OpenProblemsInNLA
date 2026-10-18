# Canonical solved-proof inventory, 17 October 2026

Independent AI-agent source audit by `/root/solved_inventory`. This is an inventory, not a new mathematical or mechanical proof-verification claim. The registry, canonical pages, original targets, IDs, indexes, and pre-existing dirty files were not changed.

`inventory.json` retains the **initial** dirty working snapshot from `/Users/ajt253/Documents/OpenProblemsInNLA` and immutable published commit `47006df8b3a6c724a557266c891893d03e69323a`. It is preserved as historical evidence and is not overwritten by the default command. Run `python3 docs/lean/campaign-2026-10-17/inventory/generate_inventory.py` to produce `inventory-current.json` for the current checkout. Use `--working-root /path/to/checkout` to inspect a different checkout or `--output /path/to/new-report.json` to select a destination. The current-working-tree portion necessarily changes with the chosen checkout and its edits; the frozen published and candidate revisions are reproducible from the retained Git objects. All 217 canonical paths come from `problem_ids.json`; review and verification copies are excluded as live proof sources.

| Snapshot | Solved | Lean verified | Partially resolved | Open | Solution claimed |
| --- | ---: | ---: | ---: | ---: | ---: |
| Initial working branch | 56 | 50 | 70 | 41 | 0 |
| Published immutable main | 42 | 76 | 62 | 36 | 1 |

The working branch is stale. It has 55 Solved entries without any canonical Lean sources; IE-06 is the exception and has a pre-existing untracked candidate project. The published snapshot has 34 Solved entries without canonical Lean sources and 31 without any live proof source, counting the shared campaign. Source presence does not establish a complete proof. There are 32 canonical status differences between the snapshots.

FR-05 is Open in the stale working branch but already Lean verified on published main. Its published full-target Gaussian/all-signals limit and stronger `C/d` bound have a recorded independent source review and isolated Linux Comparator/LeanCert kernel receipt in `docs/lean/proofs/FR-05/`. The receipt identifies PR #342, job `38000947893/114058782811`, and exactly the standard three axioms. There is no reason to re-prove or replace FR-05.

Published main has 42 remaining Solved IDs:

AA-01, AV-01, AV-02, FR-10, IE-08, IE-10, IE-12, IE-21, IE-22, IV-02, IV-04, IV-05, MD-03, MD-04, MD-06, MF-08, MI-16, NM-03, PF-04, PF-05, RA-04, RA-05, RA-10, RA-12, RA-13, RE-05, RE-06, SP-11, SP-12, TR-04, TR-06, TR-08, TR-14, TR-17, TR-20, TR-21, TR-26, IE-26, MI-31, RA-19, SP-13, SP-14.

Existing work must be reused before new proof assignments:

| ID | Later candidate revision | Actual scope |
| --- | --- | --- |
| RA-10 | `466a178a0f9ada18c054fdfd8db38e3d2a999ec7` | Full frozen Target with constant 11; later canonical status Lean verified. Dedicated receipt binds PR #359, Linux Comparator and LeanCert kernel result, and a 95-module pinned closure. Inventory has not rerun that receipt. |
| MD-03 | `fb7acabd62df62b20e2813165773a2602ac9eac0` | Full frozen Target wrapper with constant 36 over pinned `Komlos.Main`, plus promotion and receipt. Published main already has the proof source even though its proof inventory calls it statement-only. |
| MD-04 | `d9212bc43ce51a3ccdb376aa661b11d3d41f49f8` | Full frozen Target via MD-03 reduction, promotion and dedicated Comparator recheck receipt. |
| PF-05 | `6e2c960557b6f61af1ed6e679b0634dd498181b2` | Seven finite-matrix support modules, including zero-pair congruence normalization and rank-three factorization changes of basis. No `Solution.lean` or full theorem. Positive-case rigidity/topological argument and final assembly remain. |
| TR-14 | `fdb40b66425ec58e4806cee93d2aaf92a0f8597c` | 39 support modules. Local CRT/Fourier upper width and chart transport exist; binary upper width and unrestricted ordinary lower bound remain substantial missing gates. Local upper width alone is insufficient. |
| RA-19 | `0b5ac28a922c8c8768dfe043a6e282cd190bcfe8` | Independently reviewed exact proof contract only. Uniform nonempty polynomial-open witness, normal-bundle reducedness/resultant multiplicities, and actual critical-point bijection remain; there is no proof module. |

RA-10, TR-14, and SP-14 already have large shared proof programs (100, 34, and 90 Lean source modules respectively on published main). IE-21, IE-22, IV-02, IV-04, MD-06, and TR-04 retain partial canonical projects. The existing published `docs/lean/proofs/INVENTORY.md` is useful but not current for MD-03/MD-04 source presence; it must not be treated as a complete implementation inventory.

The next independent route selected by the coordinator is SP-11: its exact statement is a small concrete graph/matrix proposition and has no active proof branch among the inspected local refs. Its all-graph minimum-degree theorem remains mathematically substantive; a proof of only low dimensions, a positive-semidefinite strengthening, or a conditional orthogonal-representation lemma is not the retained target. RA-19, TR-14, MI-16, TR-20, and TR-26 should not be advertised as short certificate exercises: their canonical targets quantify over arbitrary dimensions and require algebraic geometry or substantial algebra beyond finite numerical checks.

The initial dirty tree includes AC-01 and IE-06 Markdown/TeX/PDF, generated indexes, `tools/render_problems.py`, `MOTIVATION.md`, the untracked IE-06 Lean project, and historical review directories. These were inspected read-only and preserved. The machine-readable report includes the exact observed `git status --short` boundary.
