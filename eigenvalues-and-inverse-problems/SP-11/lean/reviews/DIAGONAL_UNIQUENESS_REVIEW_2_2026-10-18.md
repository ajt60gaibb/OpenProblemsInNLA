# Independent review 2: diagonal canonical uniqueness

Reviewer: `/root/solved_inventory`, independent AI agent, 18 October 2026.
Verdict: **APPROVE** root-owned DiagonalUniqueness.lean at SHA-256
`e5ccc886ef054e7d4e39a45a867b2621a5e973836aa0979744919aa30dea3385`. I did not author or edit this module.

I read the complete source and traced its use of OrdinaryBlockers,
CanonicalOutputs and DoubleOccurrenceShape, which I previously independently
reviewed. A fresh local compile of the unchanged final source passed; all
LeanCert kernel assertions succeeded, and the final theorem's printed closure is
exactly the standard axioms `propext`, `Classical.choice`, `Quot.sound`.
[Hash-bound command and log](diagonal-review-2-evidence-2026-10-18/result.json)
record the actual run. This is not Linux Comparator acceptance or a certificate
of the complete SP-11 Target.

The general normal_tree_blockers theorem handles top roots separately from lower
occurrences. At a root, every smaller canonical output q is an actual child slot;
its original label is strictly smaller, its canonical output is q, and actual
parent tuple injectivity prevents its actual output from equaling the parent's.
At a nonroot occurrence, the source extracts its real parent and slot, then uses
the strictly ordered sibling blocker theorem. It never treats arbitrary output
colorings as injective without the explicit hinj premise.

For i=i the actual insertion cap is the complete prior-nonneighbor list length,
so the insertion slot is exactly Fin.last. Fin.succAbove_last_apply then makes
every top input retain its ordinary slot color. Nonroot inputs already obey the
normal coloring rule. This covers zero arity and the n=1 endpoint without an
extra nonempty-child assumption.

The final proof applies the actual paired-coloring recovery theorem to the two
sides of the same lssGarden. The canonical pair's sign is proved nonzero from
OrderedGreedy and the explicit dimension bound; the actual pair's nonzero sign
provides each occurrence's real tuple injectivity. Both side roots satisfy the
normal root-cap and input-slot rules just proved, so all lower-color blockers
are discharged. The equality of exact shared-label exponents is still an
explicit premise, as required for the later unique-coefficient application.
No positivity, edge hypothesis, extra genericity, new per-occurrence variable,
or assumed target theorem is introduced.

The theorem proves precisely the needed diagonal uniqueness under those stated
coefficient-comparison hypotheses. It does not itself establish edge uniqueness,
all Gram nonvanishing, or the frozen Target. No blockers found.
