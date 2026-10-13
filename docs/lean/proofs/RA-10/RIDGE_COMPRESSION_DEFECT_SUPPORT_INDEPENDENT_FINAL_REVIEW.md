# RA-10 selected compression defect support: independent imported review

**Independent reviewer:** `/root/ra10_support_audit`. **Disposition:** pass the exact support identity as a partial Lemma 2 gate. The coefficient-two ridge estimate and frozen `NLA.Statements.RA10.Target` remain open.

The reviewer audited `RidgeCompressionDefectSupport.lean` at SHA-256 `abdc5d0946a845752428c4ddee4946a3c9dc44fdd33c69f386b6e9e6fcc5a63f` against the prior [mathematical/indexing contract](RIDGE_COMPRESSION_DEFECT_SUPPORT_PRE_REVIEW.md), its [independent pre-review](RIDGE_COMPRESSION_DEFECT_SUPPORT_INDEPENDENT_PRE_REVIEW.md), the canonical README and solution, and the frozen Lean statement. The README, solution, statement, and precontract hashes are respectively `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742`, `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c`, `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82`, and `024504e972c827f4ea68046355c0da0222973d5b87a26ac9e7f1ee9b118088c8`.

The exported theorem's type matches the pre-reviewed signature verbatim. For `k ≤ n`, it uses the supplied ordered PSD witness of `Ahat`, an arbitrary ordered PSD witness of the **actual** compression `C=P*A*P`, and `c>0`; it proves

```text
tr(hermitianPositivePart(c • P − C))
  = ∑_{i : Fin n, i.val < k} max(c − eigenvaluesC i, 0).
```

This is the source's `d=tr((cI_k−H)₊)` written in the full space. The formula retains the `k−rank(C)` selected zero directions, each contributing `c`, and excludes `ker(P)`. The proof's upper bound uses the positive spectral projector of `cP−C` and a trace bound on `P−E_{h>0}`; the lower bound constructs `P−E_{h>c}`. Positive-eigenvector support and the audited zero tail make the argument valid for an arbitrary supplied witness `QC`, with no commutation, gap, or full-rank hypothesis. The pre-reviewed `C=0`, `k=0`, and rotated `2×2` witnesses remain covered.

The independent reviewer found no `sorry`, `admit`, custom `axiom`, `unsafe`, or `opaque` declaration. Its direct pinned Lean 4.33.1 / LeanCert `kernel` run passed `#assert_trust kernel`; `#print axioms` reported only `[propext, Classical.choice, Quot.sound]`. A separate exact-signature import in `/private/tmp/nla-ra10-defect-independent-audit.lean` repeated both checks, and the aggregate `lake build NLA.Proofs` passed 2,786 jobs after import. The module is an exact support gate; it does not establish the later coefficient-two positive-part bound or the full target.
