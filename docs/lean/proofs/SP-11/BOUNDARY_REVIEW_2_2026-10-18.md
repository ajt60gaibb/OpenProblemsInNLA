# SP-11 canonical package boundary — second independent approval

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I did not implement this package scaffold. **Verdict: approve the frozen
statement/Comparator boundary below for subsequent proof packaging.** This
approval is not a proof or Linux acceptance claim.

| Boundary file | SHA-256 |
| --- | --- |
| `NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `NLA/Statements/SP11.lean` | `7de112a24cb0b78894d495b840a77a58572cce574d5d77eda15381410c65b131` |
| `Reviewed/SP11.lean` | `3a294de54f52a4287ed22b80d5b0721859154b642fe3c1ac62f7d4609be38222` |
| `Challenge.lean` | `8bb9605181a095f292d2b03ed48eb8217d9c9647aae9476ee804294bcb068ac2` |
| `Identity.lean` | `942bdf685279cd9b9182367e00fac3428204490d05747e8172d353349c4dc0b9` |
| `comparator.json` | `bac828f2e95d7135346e5a48dbd07dbd65450b843860f4849739dca3c69ca2fe` |
| `lakefile.toml` | `f00c89d3dd744b0436de0d5bdc41209af4574356c6a07da1e2f6588af66905b5` |
| `lake-manifest.json` | `0695923822bec5a0513a43fa69468e8e9a561c10315dac5b317aafe2596702b1` |

The package root is `eigenvalues-and-inverse-problems/SP-11/lean`. The live
statement and infrastructure are exact copies of the reviewed shared files;
the reviewed statement, original canonical page and numerical specification
also match their source lock. The mathematical boundary is every positive
order finite simple graph, with a real symmetric matrix, an equivalence
between edges and off-diagonal nonzero entries, unrestricted diagonal, and
minimum degree ≤ natural nullity `n - rank`. This is the retained original
question, including isolated vertices and order one. There is no PSD, sign,
connectedness or regularity restriction.

`Challenge.lean` declares the single zero-parameter theorem
`NLA.SP11.target : NLA.Statements.SP11.Target`, using the deliberate comparison
placeholder. `comparator.json` selects exactly that theorem in the future
`Solution` module, has no definition holes, and permits only the three standard
foundational axioms. `Identity.lean` proves definitional equality with the
separately frozen reviewed `Target` by `rfl`. This identity verifies the
boundary; it does not prove the target. The README and metadata correctly
identify the scaffold phase and absent Solution; metadata will need updating
when the proof is actually packaged.

Fresh source compilation passed the two statement modules, reviewed module,
Challenge, Identity, and an independent consumer checking theorem kind,
printed type, Identity kernel trust and axioms. A seventh command deliberately
audited Challenge in kernel mode and **rejected it for `sorryAx`**, as required.
The placeholder is not accepted as a proof. Fifteen source-lock, copy and
resolved dependency checks passed; all ten dependency repositories matched
the pinned revisions and had clean tracked sources. All package bytes stayed
unchanged during the check, and `Solution.lean` remained absent.

```bash
python3 docs/lean/campaign-2026-10-17/verification/check-sp11-package-boundary.py
```

The source snapshots, positive/negative consumers, compiler identity, all
raw logs and machine-readable result are retained in
`docs/lean/campaign-2026-10-17/verification/sp11-package-boundary-review/`.
The first checker attempt incorrectly required irrelevant manifest inheritance
and requested-ref metadata to equal the shared package; its result is retained
as `attempt-1-result.json`. The corrected check compares resolved package names,
URLs, types, subdirectories and commit revisions, all of which agree. There
was no source or Lean failure in that first attempt.

No package source was changed for this review. This is independent AI-agent
review and local macOS elaboration/kernel evidence with pinned cached
dependencies. It is not external human peer review or Linux Comparator
evidence. After proof packaging, the exact completed Solution and imported
closure require separate fresh proof and real Linux verification.
