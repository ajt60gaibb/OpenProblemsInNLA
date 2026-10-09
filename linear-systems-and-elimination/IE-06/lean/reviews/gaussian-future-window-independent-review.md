# Independent exact-source review: GaussianFutureWindow

Reviewed by the source-statement author independently of root implementation. Source SHA-256 `f594e4d08ee4bd4fc4d3252f0dea91c22b766e7bd10f3b189442789aaf304262`.

Approved. The explicit `windowIndex` maps the first s suffix offsets to original columns t through t+s−1 and keeps later original labels unchanged. Its inverse separates precisely those two ranges. Both pointwise inverse identities and coordinate measurability are proved. Product-coordinate reindexing, a sum/product split, and transposition give the exact law Gaussian n×s times the remaining future law. No conditioning or row selection enters this module. The argument includes s=0 and t+s=n without nonempty assumptions.

Independently rebuilt GaussianCoordinates and this module with unchanged pinned Lean 4.33.1 dependencies. Both builds exited 0, with no warnings or nonfoundational axiom. The nine kernel assertions passed; printed theorem dependencies were only propext, Classical.choice, and Quot.sound. Log: `/private/tmp/ie06-future-window-independent-check.log`.
