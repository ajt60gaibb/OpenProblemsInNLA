# Independent actual top-occurrence and edge-uniqueness review

Reviewer: `/root`, OpenAI Codex AI agent, 18 October 2026. **APPROVE**
`TopOccurrences.lean` and `EdgeUniqueness.lean` at the hashes in the evidence
below. I did not implement these two modules. This does not independently
review my own final assembly or replace Linux Comparator verification.

The top occurrence list is literal: its inserted slot is the earlier actual
root and every other slot is the corresponding actual child of the later
root. The cast helpers transport only proved root-label and arity equalities.
Under adjacency the earlier root cannot already be a later nonneighbor.
The list's labels therefore equal the true sorted augmented predecessor list
and are strictly increasing. Its colors are a reindexing of one actual
later-root incident tuple: the earlier root output is the shared cap, not an
independent choice. A nonzero sign makes that entire tuple injective.
Canonical outputs equal the augmented slot indices, so every smaller color
has an actual earlier-label blocker. Both end insertion positions are included.

The final edge proof covers every actual occurrence. The earlier top root
uses the augmented blockers; its proper descendants use ordinary parent
siblings. The later top root is tied to the earlier top root at a strictly
smaller label. Its immediate children use the augmented blockers, and all
lower descendants use ordinary parent siblings. Parent existence is proved
from the actual tree, and the nonroot condition distinguishes the exceptional
top parent. No occurrence is omitted and no local shape premise survives.

Actual class sums and strict child descent now discharge the generic recovery
theorem. Exponent equality is for the original shared Sigma(vertex,subset)
variables, with repeated occurrences retained. Equality of all recovered
outputs gives equality of the actual paired summand index. Only nonzero-sign
summands are constrained; zero-sign summands may share the exponent and do
not contribute. This proves the precise uniqueness needed for coefficient
isolation, without asserting independent variables at repeated occurrences.

I read the complete sources and independently recompiled both unchanged files
with the pinned runtime. Their LeanCert kernel assertions passed and printed
axiom closures contain only the three permitted foundational axioms. Exact
hashes, return codes and logs are in
[`top-edge-root-evidence-2026-10-18/result.json`](top-edge-root-evidence-2026-10-18/result.json).
This is supporting macOS source compilation using pinned imports; the
independent fresh-closure audit is separately retained by the verification
agent. No authoritative Linux claim follows from these local logs.
