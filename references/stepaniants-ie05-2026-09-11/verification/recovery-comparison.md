# Later recovered IE-05 variant: exact equivalence review

**Verdict: PASS as a corroborating reconstruction of the same counterexample, not another solved problem.**

Reviewed by Codex agent `/root/prepare_manuscripts` on 11 September 2026, after the canonical solution and its PDFs were frozen. No mathematical text or publication PDF was changed as a result of this comparison.

The later supplied [reconstructed manuscript](../recovery/solution.md) has SHA-256 `a3ba2afb7bac18bc2cb6594b194755be32203324a01bbab460507b8c9af53c2d`. It replaces entry `(7,2)` of `L_8` by zero, whereas the existing [reviewed proof](../full-proof.md), SHA-256 `18d49f30a3ef26f4c88a85c8ea1fc9e5c4e1702b4be6061d39aec892e96a4af7`, replaces `(8,2)` by zero. The displayed canonical baseline matrix is identical in both manuscripts.

## Exact QR relation

Let `P` interchange rows 7 and 8, let

$$
J=\operatorname{diag}(1,1,1,1,1,1,-1,1),
$$

and let `K` be the identity except for `K_{77}=-1` and `K_{78}=1`. If `L` denotes the existing input and `L_*` the recovered input, direct multiplication gives

$$
L_*=PLK.
$$

For the positive-diagonal QR factorization `L=QR`, therefore,

$$
L_*=(PQJ)(JRK).
$$

The first factor is orthogonal. The second is upper triangular and has positive diagonal: the two minus signs at diagonal position 7 cancel, and all other diagonal entries remain positive. Uniqueness of this QR convention yields

$$
Q_*=PQJ.
$$

The separately written [exact relation checker](verify_recovery_relation.py) parses both printed integer-column matrices and confirms `M_*=PHJ` entry by entry. Their corresponding column squared norms are identical, so this is the exact relation between the normalized orthogonal matrices too.

## Why the growth ratios coincide for these tie paths

Row permutation alone does not justify preserving growth under a fixed tie rule. Here one can check the whole path. Through the first six pivots, the row interchange lies entirely within the active rows; the column-7 sign commutes with the elimination updates. For stages 1 through 7 the two active matrices are consequently related by the restricted row interchange and column sign. Their entrywise maximum magnitudes coincide. Each diagonal pivot remains positive and first among the largest-magnitude entries of its active column.

At stage 7, before applying the identical positive column normalizations, the remaining blocks are respectively

$$
\begin{pmatrix}3063&2683\\-3063&2589\end{pmatrix},
\qquad
\begin{pmatrix}3063&2589\\-3063&2683\end{pmatrix}.
$$

Both first-row pivots are admissible, their final multiplier is minus one, and their final pivot is `(2683+2589)/sqrt(5272)=sqrt(5272)`. Thus all eight active-stage maxima agree. Their input maxima also agree, as is immediate from `Q_*=PQJ`. Both growth factors equal `5272/63`; the recovered cross-product difference is the unreduced form of the same positive squared growth gap.

The [exact comparison output](recovery-relation.json) records the matrix identities, both stage-7 blocks, all eight normalized maxima, QR diagonal signs and the common ratio. This verifies equivalence of the actual legal first-available-row paths, not merely similarity of decimal outputs.

## Supplied certificates and provenance

I read both supplied programs before execution. The [rational Gram-Schmidt program](../recovery/verify_exact.py) reconstructs the exact QR factors and all elimination stages; the [second program](../recovery/independent_check.py) reconstructs Schur complements by leading-block inversion. Neither imports the other. Rerunning them reproduced the supplied [certificate](../recovery/certificate.json), SHA-256 `763c0c84ff76f6aafea9d38d39ab47cbf58787d464209ad601ee62970bfedf8c`, and the second transcript byte-for-byte. The [rerun records](recovery-source-checks.json) and [program output](recovery-verifier-rerun.txt) retain this evidence; [second program output](recovery-independent-rerun.txt).

The supplied [recovery notes](../recovery/RECOVERY_NOTES.md) explicitly describe reconstructed files rather than an untouched historical archive. This review verifies the present mathematical source and certificates, not the accuracy of unobserved historical recovery events, prior publication or priority. The recovered PDF and TeX layout were not audited here and are not republished in this supplementary record. The existing reviewed and visually checked canonical documents remain the submission artifacts.

Reproduce the independent relation check from the repository root with:

```bash
python3 references/stepaniants-ie05-2026-09-11/verification/verify_recovery_relation.py --current-proof references/stepaniants-ie05-2026-09-11/full-proof.md --recovered-proof references/stepaniants-ie05-2026-09-11/recovery/solution.md --output /tmp/ie05-recovery-relation.json
```

This is independent automated-agent review, not external human peer review or formal proof certification. The later reconstruction is retained as corroborating provenance within the existing IE-05 submission; it neither creates a second IE-05 submission nor changes the resolved-problem count.
