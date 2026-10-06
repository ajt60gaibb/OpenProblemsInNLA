# B4 numerical absorption: implementation record

The exact contracts, including C_A, D_beta, H, C_beta, x0, x, theta, and the fixed stacking threshold, were independently approved before implementation in `selected-block-extension-specification.md`. Root explicitly assigned this bounded numerical subtask to the infrastructure/Gaussian agent after that approval. This file records the ownership before implementation; the source-proof agent retains actual selected-block probability assembly.

Owned module: SelectedBlockExtensionScalars.lean. It proves the dimension/positivity guards, the A3 term bound by exp(-x), the exact source threshold bound by GaussianStackingTail.stackingThreshold, and the final probability accounting bound. The scale a is the explicit formula sqrt(GaussianAppend.appendConstant) * mu^-1 * exp(x0/k), definitionally the already implemented SelectedBlockAppend.appendScale. No additional probabilistic result is assumed or implemented here.

The constants remain D_beta=64(beta+6), H=1+sqrt(C_A)+24*exp(1)*(1+50*sqrt(C_A)), and C_beta=D_beta+2beta+6+log(2H)+1. The final public target retains its non-strict bad event and exact factor (mu*d/k)exp(-C_beta*(1+klogn/d²)). All inequalities are symbolic kernel proofs; no huge dimension is evaluated numerically.


Completed source SHA-256: `8142f8f4ebf1c7ab4e15728874b42e0e68526c67319d8ccef79ad666cf457a0f`. Direct pinned Lean 4.33.1 compilation passed for all 28 declarations; every declaration has #assert_trust kernel and prints only the three foundational axioms. No warning was emitted by this module. The parent independently read and approved the complete implementation, including the floor-index count, the exponential overcrowding bound, product/compression thresholds, reciprocal half-factor, and combined budget. A complete 58-module transitive source closure is separately recorded under `selected-block-extension-scalars-compilation/`; only a successful receipt establishes completion of that broader check.
