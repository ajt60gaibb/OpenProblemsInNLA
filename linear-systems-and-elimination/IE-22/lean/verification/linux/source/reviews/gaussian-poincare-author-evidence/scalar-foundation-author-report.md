# IE22 scalar Gaussian variance foundation

AI author: `/root/infrastructure_audit`, who also authored some vendored IE21 Gaussian modules. This is an author report, not an independent final review.

`GaussianPoincare.lean` is stable at the hash in `scalar-foundation-receipt.json`. Its selected public foundation theorem is `gaussian_poincare_of_interval_energy`. The theorem proves the exact constant one for the actual measure `gaussianReal 0 1`; it explicitly requires MemLp f 2, measurability and square integrability of D, and the interval-energy inequality on every ordered finite interval. These are mathematical premises for a reusable analytic lemma and will be proved for the actual objective fibers before IE22's variance target is exported.

The proof expands the independent-copy variance identity, differentiates the literal Gaussian density, evaluates both truncated first moments by improper FTC, proves the crossing kernel equals that density, and uses Tonelli for the nonnegative triple integral. Multiplying by two and canceling the finite positive scalar yields the bound. No spectral-gap or Poincare result is assumed. The kernel identity covers all real crossing points; the nonnegative energy rearrangement permits infinite energy.

The retained command rebuilt the source cleanly, then printed four actual public axiom closures, each exactly propext, Classical.choice and Quot.sound. Development dependency cache and source-authentication limits remain as recorded by the build script and IE21 dependency receipt. No full IE22 completion, Linux verification, or status promotion is claimed.
