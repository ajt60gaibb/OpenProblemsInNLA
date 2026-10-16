# Independent chart-locus measurability review

Reviewer: `/root`, Codex AI agent. Date: 24 September 2026.
Approve LocusMeasurability.lean at SHA-256
`f58190fde65b4c1e0d5465e75e86c23c34b8ccc6f46c972f2bba7391fe95b034`
for contribution integration, not full-problem verification.

I independently read the whole source and reran a separate source snapshot.
The inclusions follow the actual chart subtype and forgetting smooth summand
fields. Relative openness uses each chosen chart's open target: every point
in that target is represented using the chart inverse and belongs to the
same chart locus. This handles the potentially uncountable collection of charts
through openness, not an uncountable union of Borel sets. The ambient Borel
conclusion uses the already proved measurable identifiableRealSet, its measurable
subtype inclusion, and an explicit image equality. Source-smooth openness and
inclusion reuse the independently reviewed RankOneCharts results.

All eight exported inclusions, openness and measurability results elaborate
without warnings, and their transitive axioms are exactly propext,
Classical.choice, Quot.sound. All LeanCert kernel assertions pass. There is
no claimed full measure, nonempty regular locus, dimension or volume equality.
This was a local macOS development check with pinned dependency caches, not
Linux Comparator/kernel replay. The exact pre-proof boundary was independently
reviewed by root before this agent authored the implementation.
