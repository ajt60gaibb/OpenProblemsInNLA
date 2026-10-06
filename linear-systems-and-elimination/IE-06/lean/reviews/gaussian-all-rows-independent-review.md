# Independent exact-source review: GaussianAllRows

Source-statement author independently read the entire source, checked its stage and final-transfer interfaces, and rebuilt it. Source SHA-256 `694d95262b15ebdf3b851d9717f0cb9be0d4a3ac6f81e0a727f0688ebc771418`. **Approved.**

The actual bad-row event quantifies exactly the padded stages indexed by Fin n used by all-Schur growth. On the proved Gaussian nonsingular set, early stages k<=5r have Euclidean row norm at most row l1 norm at most 2^k<=2^(5r), which is bounded by the displayed rowBound when tau>=0,x>=0. For a later stage, t=k−4r satisfies r<t and t+4r=k<n, so the proved stage estimate applies. If the simultaneous retained-inverse bad event is absent, its guard holds at this exact t. The 4r smoothing threshold is at most the common 5r bound. This gives the asserted almost-everywhere subset without conditioning on simultaneous success.

Unioning at most n stage events gives precisely (2n²+n)exp(−x). The existing all-Schur Gaussian column transfer adds 2n³exp(−x), and the exact input-normalization exception contributes ofReal(q^(n²)). The resulting growth_tail statement retains the actual worst-over-admissible-path exceedance event from the original target. No new rank, measurability, or probabilistic input is assumed.

Independent pinned Lean 4.33.1 rebuild exited 0, with no warnings. All eleven kernel assertions passed; the printed full growth theorem depends only on propext, Classical.choice, and Quot.sound. Receipt and log: `gaussian-all-rows-independent/`.
