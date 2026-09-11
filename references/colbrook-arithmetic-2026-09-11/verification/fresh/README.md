# Fresh certificate checks - 11 September 2026

The original C++ source was compiled unchanged with portable LLVM-MinGW (release 20260908), C++17, optimization `-O3`, and Boost 1.86.0. The full-matrix verifier used four threads (fewer for the smallest orders); the range checker used its original single-threaded traversal. Boost emitted compatibility/deprecation warnings, not compilation errors. Original sources and data remain unchanged in the submitted archive.

- [Full-matrix checks](full-matrix-checks.log): complete matrices, not just supplied cofactor products. Both coprime residues and the uniqueness bound are required.
- [Unrestricted-range inclusion](range-checks.log): exhaustive coverage with the proved prefix bound, using the exact witnessed catalogue for each order.
- [Data and negative tests](data-tests.log): 5,528 spectral witnesses checked with arbitrary-precision subset DP, small direct-permutation comparisons, 120 random matrices, deliberately incorrect claims, malformed matrices and omitted attainable range values. The only execution adaptation adds `.exe` to the two checker filenames on Windows; test logic is unchanged.

The permanent and range logs must contain PASS records for every order 1-35 and 1-10 respectively. The final submission validation checks those exact sets before publication. Empty `rangeN_witnesses.txt` files are normal: the inclusion checker found no uncovered values to record. Restricted membership comes from the separately checked original witness matrices, not those empty files.

The [analytic review](../reviews/AC-11-12-review.md) states its computational acceptance condition explicitly. These fresh runs discharge that condition only for the finite orders actually checked. No all-orders solution follows. Original search/solver reports outside these tests have not been rerun; AA-01's missing software is separately disclosed in the [submission record](../../README.md).
