# Independent generic-unramified contribution review

Reviewer: root, nonauthor. APPROVE GenericUnramified.lean SHA256 `3a696638c3fc0ab4216f4114712308485143137a5c2fef3011da7e52bd792dbf`, definitions SHA256 `ff8317d3fcb8ec4c29a5be165f02bd8dd3c8fc794133f90dca6e8ec4888de97f`, exactly matching the independently approved pre-proof boundary.

Full proof read. Injectivity installs faithfulness and the canonical zero-prime stalk map; generic quasi-finiteness supplies the finite residue-field extension. The base residue field inherits characteristic zero through its actual fraction-field instance. Separability then follows by the pinned perfect-field instances, and the local criterion explicitly proves the zero-ideal/maximal-ideal equality.

The localization proof starts from a nonzero source denominator in the unramified locus. A finite Zariski Main envelope clears its denominator to a nonzero integral element a=t^m*s; an integral relation supplies a nonzero base multiple divisible by a. Thus the resulting base element's image is divisible by s, giving the correct principal-open containment. The proof transports formal unramifiedness through the actual canonical localization equivalence and compatible base scalar action. It never claims the base denominator and source denominator define equal opens, or claims finiteness for this same denominator.

Both exact propositions compile in a fresh copied-source rerun without warnings; standard-three closures and LeanCert kernel assertions pass. Pinned dependency caches are reused. The actual analytic derivative and complete-target correspondence remain separate, and no Linux Comparator or complete TR-06 status is claimed.
