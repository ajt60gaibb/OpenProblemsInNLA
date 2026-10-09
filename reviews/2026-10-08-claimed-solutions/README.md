# Audit of the three solution-claimed entries — 8 October 2026

This review covers every canonical entry that had `**Status:** Solution claimed`
at the start of the audit: FR-05, MD-01 and MF-23. Codex agents read the
primary proofs and compared their conclusions with the retained targets.
These are informal AI-agent audits, not external human peer review. A separate
Lean evidence check applies the catalog's stricter `Lean verified` criteria.

| Entry | Mathematical proof audit | Catalog decision |
| --- | --- | --- |
| [FR-05](FR-05.md) | Full 13-page manuscript read; no gap found | Solved; formal verification still pending |
| [MD-01](MD-01.md) | Target bridge checked; the mixed-moment remainder needs a sharp `O(sqrt(n))` correction and printed Definition 4.3 falsifies an intermediate lemma. A [partial Lean attempt](../2026-10-09-md01-lean-attempt/README.md) checks setup and a witness, but the main theorem remains unproved | Remains Solution claimed |
| [MF-23](MF-23.md) | Two independent reads of the direct 12-page proof; no gap found | Solved; Lean evidence evaluated separately |

The permanent IDs, canonical README paths and original mathematical targets
are unchanged. An inconclusive audit is not a finding that a theorem is false.
