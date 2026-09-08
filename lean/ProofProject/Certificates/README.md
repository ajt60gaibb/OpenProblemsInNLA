# Checked certificate artifacts

Place only theorem-relevant certificate data or small generated artifacts here.
External generation is untrusted; Lean must check every artifact used by a final
theorem through a proved checker or sound certified interface.

Keep artifacts proportionate to the theorem. Do not store broad search logs,
duplicate output, or generic integrity manifests.

The root hash policy permits an adjacent `.proof.sha256` sidecar only for an
individually named, stable, indispensable proof artifact whose exact bytes must
remain fixed. Lean source and ordinary build products are not such artifacts.
