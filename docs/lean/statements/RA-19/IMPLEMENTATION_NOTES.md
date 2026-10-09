# RA-19 implementation correspondence

Author: OpenAI Codex AI agent `/root`. Both inventory and statement_design approved the exact specification before this code was written.

Square d denotes every complex order n=d+3, preserving precisely n>=3. DetDifferential uses the pinned actual Matrix.adjugate and ordinary trace/product, so its value is trace(adj(X)*Z), the determinant directional derivative even at singular X. No inverse or conjugation occurs.

SmoothPoint requires both original equations and a direction within the fixed-zero hyperplane where this derivative is nonzero. As justified in the specification and source Lemma2, the restricted determinant is a nonzero squarefree polynomial; the hypersurface Jacobian criterion gives exactly this smooth-locus predicate. Critical quantifies every tangent direction Z with its (0,0) entry zero and determinant derivative zero, and tests the full same-index bilinear displacement sum. The common nonzero derivative factor2 is immaterial.

The generic locus is witnessed nonvanishing of an actual multivariate polynomial in all matrix entries, with an explicit nonvanishing matrix witness. Every matrix in that locus must have its full Critical subtype equivalent to Fin(5*(d+3)-7). This certifies finiteness and the exact count of distinct points, rather than the count of a chosen list or only solutions of a resultant. No rank, isotropy or generic-normal-form conditions discard critical points.

Live compilation passed the shared kernel statement/trust checks with only propext, Classical.choice and Quot.sound. Final independent review must bind all actual imports, live/frozen sources and pins. No ED-degree proof, numerical root computation or Linux result is asserted.
