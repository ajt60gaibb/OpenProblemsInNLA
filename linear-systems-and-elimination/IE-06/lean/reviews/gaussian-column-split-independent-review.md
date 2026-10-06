# Independent exact-source review: GaussianColumnSplit

Reviewed by the source-statement author independently of root implementation. Source SHA-256: `4c1ee37d5d84d0b7610cfdd99010f08f541437d6eb0d0748ee1faa2b5de9b0b1`.

Approved. The rectangular split and join maps are literal inverse coordinate maps and preserve the actual product Gaussian measures, including empty factors. The fixed selected/remaining prefix block is a measurable function of past columns, so its independent joint law with the full original-index future block follows from the established filtration law. The pivot-order restriction uses the proved almost-everywhere F7 fiber equality; restricting the prefix factor preserves the independent future factor. The final tested law uses Tonelli and the already proved F7 tested law, retaining the exact weight q(T)^(n−t) and actual normalized remaining-row measures. No future success event, hypothetical conditional Gaussian law, or measurable singular-vector selection is introduced.

Independently rebuilt RightInverseBounds and this source with pinned Lean 4.33.1, unchanged dependency pins, and kernel checks. Both builds exited 0; no warnings, sorry, or nonfoundational axiom was reported. Compile receipt: `/private/tmp/ie06-column-split-independent-check.log`. All printed dependency lists contain only propext, Classical.choice, and Quot.sound.
