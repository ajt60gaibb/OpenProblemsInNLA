# TR-13 implementation correspondence

Author: OpenAI Codex AI agent `/root`. The two independent preimplementation approvals were available and bound to the final specification before this source was written.

The reviewed TR14 module supplies the original Hankel coefficient indexing and full ordinary/symmetric width decompositions; it is in the transitive review closure. VandermondeVector uses i=0,...,n-1, so the natural subtraction n-1-i never underflows on the n>=2 target domain. Nonzero projective pairs allow either coordinate alone to vanish, including infinity. Coefficients can vanish and each finite sum permits zero padding.

OrdinaryBorderWidth quantifies arbitrary tensors in a sequence; there is no symmetry or Hankel constraint. SymmetricBorderWidth quantifies symmetric decompositions, imposing no Hankel restriction. Both use every-coordinate Tendsto in the ordinary complex topology. EqualFiveRanks compares all four other width predicates to ordinary width for every r, retaining r=0 and therefore the exact rank minima.

Target universally retains odd m>=5 and n>=2, then existentially chooses an actual MvPolynomial on all Hankel coefficients and an explicit nonvanishing evaluation witness. Its nonvanishing locus is a principal Zariski open. Existence of such a nonempty locus is equivalent to existence of some nonempty open subset because a nonempty open has a point outside its complementary common-zero set and at least one defining polynomial is nonzero there. The conjecture is required on this full locus, not at one chosen point or finite sample. The separately known generic rank value is not inserted as an extra target conjunct.

Both actual live modules compiled using pinned Lean 4.33.1 and the exact cached Mathlib/LeanCert dependency revisions. Kernel statement/trust assertions passed with only propext, Classical.choice and Quot.sound. These are statement definitions; no Target theorem is asserted. Final live/frozen review and Linux Comparator identity checks remain separate gates.
