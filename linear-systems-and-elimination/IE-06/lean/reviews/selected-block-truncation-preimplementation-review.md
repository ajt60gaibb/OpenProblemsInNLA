# Exact padded truncation: preimplementation contract

The coordinator approved these exact formulas before implementation, after the
independent mathematical review agent proposed and checked them. Let the actual
prefix be nonzero, pi=pivotOrder ht A, T=selectedBlock ht pi A, and suppose
T^-1=Z+H V^T with V^TV=I_q. Let P be the n-by-t coordinate embedding
P(j,a)=1[j=pi(a)]. Put Q=P V. Let R's active row i be the first t entries of
the original row labelled rowLabels(firstPath A)t i; set inactive rows of R
to zero. Let I_active have the corresponding original-label identity rows,
with inactive rows zero. Define X=I_active-(R Z)P^T and Y=-R H.

Prove Q^TQ=I_q, E_t=X+YQ^T, and for each active i,
rowNorm(X,i)^2=1+norm(z_i Z)^2; inactive X,Y rows are zero. These are exactly
the coordinate formulas proposed to root. The embedding P is isometric because
pi is injective; the row-norm formula uses disjoint selected labels and the
active original identity label. The inverse decomposition and previous exact
selected-block row identity give E=X+YQ^T by ordinary matrix distributivity.

The discarded rank q is arbitrary, and zero dimensions retain literal meanings.
No randomness, measurable spectral choice, independence, or probability bound
is part of this deterministic bridge. Later arguments can choose Z,H,V for each
fixed selected block and integrate an intrinsic event. The coordinator will
independently review the implemented proofs.

Completed implementation: `NLA/IE06/SelectedBlockTruncation.lean`, SHA-256
`7fe02fa5560c5ee8e21d8820817d03c65218f559cc067771dd622b300a89eb47`.
All 17 local declarations passed individual LeanCert kernel-policy checks and
printed only foundational axioms (propext, Classical.choice, Quot.sound), with
no warnings. The private pinned-runtime local-cache receipt/log are under
`reviews/selected-block-truncation/`; no fresh dependency rebuild/replay is
claimed. The coordinator will independently review this frozen code.
