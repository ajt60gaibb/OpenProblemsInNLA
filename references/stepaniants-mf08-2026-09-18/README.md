# MF-08 — literature resolution

**Literature application and curation:** George Stepaniants, Department of
Computing and Mathematical Sciences, California Institute of Technology.

The original [MF-08 question](../../matrix-functions-and-stability/MF-08/README.md)
asks for polynomial-time many-one NP-hardness of strict Hurwitz stabilization
with rational plant matrices and an unrestricted real static feedback gain.

Johan Löfberg's [Theorem 1.1, arXiv:2609.16886v1](https://arxiv.org/html/2609.16886v1)
(15 September 2026) proves hardness on integer single-input plants.
Amir Ali Ahmadi, Abraar Chaudhry, Ijay Narang and Yukai Tang's
[Theorem 1, arXiv:2609.20636v1](https://arxiv.org/html/2609.20636v1)
(17 September 2026) proves strong hardness on integer single-output plants.
Both quantify over unrestricted real gains and use strict Hurwitz stability.
Each subclass embeds into MF-08 by writing integers as rationals with denominator
one. This polynomial inclusion leaves feedback feasibility unchanged, so either
source settles the whole original target. No NP-membership claim is needed.

The mathematical resolutions are the cited authors' results. This note supplies
their application and catalog curation; it claims no new theorem or discovery
priority for George Stepaniants.

The sources are v1 preprints. The [independent review summary](review-summary.md)
records a separate Codex-agent audit of the complete continuous-time proofs.
No journal acceptance, external human peer review or formal verification was
established. The papers themselves are linked, not redistributed.

On 18 September 2026, the final refreshed check covered 16 accessible public
repositories, 274 branch heads and 227 complete immutable tree listings. New
commits retained the unchanged MF-08 statement with status Open. Target-named
file scans and four all-state upstream PR searches found no competing submission.
The upstream base was `71563f17926cd826a892c2bba0e294894ee57a5c`.
The [dated search record](public-audit.json) gives the scope and evidence hashes.
This is a dated public-source check; private, deleted, unreachable or differently
named work is outside its scope. The inventory is not an atomic GitHub snapshot.
