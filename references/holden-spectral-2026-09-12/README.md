# Spectral partial results and supporting reductions — Sidney Holden

**Author:** Sidney Holden.  
**Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation.  
**Date:** 12 September 2026.

## Verified affiliation and attribution

The [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/), accessed 12 September 2026, identifies Sidney Holden as a Flatiron Research Fellow in Biological Transport Networks, CCB, Flatiron Institute. The current [CCB staff directory](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport&type=ccb-staff) corroborates this. The older Edinburgh student profile is not used as a current affiliation.

Authorship is recorded at the author's explicit request. The supplied manuscripts disclose AI-assisted derivation and self-review; additional Codex AI assistance prepared this submission. Separate Codex agents independently audited the mathematics. These are informal automated audits, not external human peer review or formal verification. No Lean verification was performed. Attribution to the original problem authors and cited prior results is retained; no novelty or priority claim is made.

## Scope and review

| Entry | Included result | Proposed status | Independent audit |
| --- | --- | --- | --- |
| KE-02 | [Theorems A and B, Section 5](KE-02/proof.md): weak coupling, constant diagonal/equal off-diagonal magnitudes, and order two | Partially resolved | [KE-02 review](verification/KE-02-review.md) |
| SP-08 | [Finite spread cases and reduction](SP-08/proof.md): (8,1/2), (10,0), (11,0) | Partially resolved, retained | [SP-08 review](verification/SP-08-review.md) |
| SP-09 | [Theorem 1 and amplification corollary](SP-09/proof.md): at least one spectrum has at most two points | Partially resolved, retained | [Independent review](verification/SP-09-SP-07-SP-03-review.md) |
| SP-07 | [Two-point subclass matching lemma](SP-07/result.md) | Open, retained | [Independent review](verification/SP-09-SP-07-SP-03-review.md) |
| SP-03 | [Skew-multiplier reduction](SP-03/proof.md), without a new generic degree count | Open, retained | [Independent review](verification/SP-09-SP-07-SP-03-review.md) |

No full original target is resolved. KE-02 still asks for arbitrary normalized Hermitian tridiagonal inputs outside the proved classes; SP-08 still asks for all dimensions and interval parameters; SP-09 remains unresolved when both spectra have at least three distinct values. SP-07's global optimum and SP-03's all-ranks degree formula remain open. All five entries continue to count as open targets.

## Duplicate and eligibility screen

The submission branch starts at upstream main `f41f1f9ffa2171550d4bb795862c6170c4f26070`. The upstream pull-request listing (all states, 100 limit; fewer than 100 results) and fetched upstream/fork histories were checked on 12 September 2026. None of these five IDs has a previously pushed full solution in those histories or PRs. Their current canonical statuses are Open or Partially resolved, and their changes since admission are editorial/status audits, not full resolutions. Existing cases cited on each page remain credited. This screen does not establish publication novelty.

The other eight supplied entries (IS-01, SP-01, SP-02, IE-07, IS-04, IS-05, SP-10, SP-14) contain target/status notes without a new theorem. They are not submitted as solutions and their pages are unchanged. Attached handoff instructions were treated as source content, not as authorization or a substitute for independent review.

## Source preservation and reproduction

The five selected problem folders come from `OpenProblemsInNLA_status_improvement_candidates`. [Original SHA-256 hashes](source-sha256.json) identify supplied files before adding author/affiliation headers and normalizing GitHub math delimiters/operators in proof/result manuscripts. Historical self-review and logs remain explicitly historical. [Source notes](sources/REFERENCES.md) and [pinned target metadata](sources/snapshot.json) are supplied provenance, distinct from the new independent reports.

The three SP-08 certificates are losslessly gzip-compressed to keep the contribution compact. Decompress them in place before using the unchanged commands in [the verification guide](SP-08/verification/README.md):

```bash
python3 - <<'PYCODE'
from pathlib import Path
import gzip
for p in Path('references/holden-spectral-2026-09-12/SP-08/certificates').glob('*.json.gz'):
    p.with_suffix('').write_bytes(gzip.decompress(p.read_bytes()))
PYCODE
```

The decompressed bytes must match `source-sha256.json`. Python 3.10 or newer is needed for KE-02 annotations; SP-08 uses NumPy/SymPy as listed in its requirements. Independent reports distinguish proof review, complete certificate coverage, and finite diagnostics. No numerical experiment alone is treated as a proof.
