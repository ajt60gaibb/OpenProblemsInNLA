# Gaussian concentration wrapper: exact preimplementation contract

Root proposed and /root/source_statement_author independently approved this
contract in team messages before implementation. The upstream law must equal
Mathlib stdGaussian on EuclideanSpace R (Fin n), proved via the actual product
Gaussian pushforward. For every n (including zero), L:NNReal and LipschitzWith L f,
f is integrable under that law. For x>0, its strict centered upper tail at
L sqrt(2x) is at most ENNReal.ofReal(exp(-x)). Handle n=0 and L=0 as constant
functions. In the positive cases use the reviewed upstream non-strict tail
and exact exponent identity. No concentration or integrability premise may be
added. This wrapper alone does not establish the matrix spectral tail.
