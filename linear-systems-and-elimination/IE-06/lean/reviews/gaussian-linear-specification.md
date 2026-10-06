# Gaussian linear forms: preimplementation review

Author `/root`; independent approval by `/root/source_statement_author` before
implementation. For the actual product standard Gaussian vector in dimension d,
prove the exact moment integral of exp(t sum_i v_i z_i), including integrability,
as exp(t² sum_i v_i² / 2). Derive the explicit directional subGaussian property.

For x>0, prove the strict two-sided tail at sqrt(2x sum_i v_i²) is at most
2 exp(-x). Zero variance means every coefficient is zero, so the strict event
is empty; dimensions zero are covered. For m deterministic row vectors with
squared norms bounded by L≥0, enlarge the threshold to sqrt(2xL) and use a
finite union bound to get 2m exp(-x). The rows need not be independent. These
are exact Gaussian inputs for the fresh-column part of the proof, not an
assumed adaptive independence theorem.
