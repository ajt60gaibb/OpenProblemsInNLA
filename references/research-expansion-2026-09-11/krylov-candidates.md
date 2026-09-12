# Krylov, conditioning and elimination search — 2026-09-11

Admitted entries (see the [admission record](README.md) for final IDs and scope):

1. [Perturbed Fourier stability](../../linear-systems-and-elimination/IE-26/README.md): grouped Austin–Trefethen infinity- and two-norm conjectures. Strong latest status: Chen–Lin–Zhang arXiv2608.21960, 22 August 2026, proves the two-norm exponent up to a logarithm and matching lower exponent. Yu–Townsend DOI and BIT63(2023), article23, verified in its arXiv metadata. The final normalized matrix was independently checked against equation (1.6) of the 2026 paper.
2. [Radau spectral disk](../../linear-systems-and-elimination/IE-27/README.md): Axelsson–Dravins–Neytcheva Conjecture 1, source proof for two stages, general-stage open statement repeated by Outrata's 2025 preprint (published 2026). Draft transparently specifies the symmetric elliptic setting used by the later analysis. The original word "positive definite" is broader/ambiguous when discussing convection; do not silently generalize to arbitrary nonsymmetric matrices. The final page retains this explicit source-supported specialization.
3. [Positive diagonal nilpotent stiff limit](../../linear-systems-and-elimination/IE-28/README.md): van der Houwen–de Swart 1997 §3.2.1 conjecture, explicitly still unproved for arbitrary stages in Čaklović et al. SISC2025 §2.2.3. Draft formalizes the positive-distinct-node model from the original §3.2.2 and newer paper; zero nodes would trivially invalidate the unqualified statement. No ordering of the diagonal is imported from the newer algorithm.

All three are absent from CATALOG.md, SCREENED-OUT.md and the September literature-expansion reserve. Existing FR-02 concerns RIP on selected equispaced Fourier columns; IE-16 concerns a minimax bound for normal GMRES; neither duplicates the perturbed square Fourier matrix target. IE-24/25 concern incomplete factorization for spatial Neumann problems rather than fixed small collocation matrices. No shared registry/index or existing canonical page was edited.

## Other leads not admitted

- Knyazev LOPCG rate conjecture: modern explicit statements in Shao–Chen–Bai, *EPIC*, SIMAX46(2025), equation (5.16), and Ming Zhou, NLAA2026 DOI10.1002/nla.70078. The original Knyazev2001 equation (5.5) appears to concern an average/asymptotic reduction, and modern printed formulas have normalization ambiguities. Do not admit a universal per-step contraction without checking the original algorithm and rate quantifiers. This remains a useful separate research lead.
- Knizhnerman–Simoncini extended-Krylov Lyapunov rate conjecture is already reserved for uncontrolled constants and finite-dimensional vacuity. Not recycled.
- Liesen–Tichý roots-of-unity 4/pi conjecture is IE-16, not new.
- Yuan–Zontini Gauss–Seidel preconditioner comparison has a 2019 proof lead, not admitted.
- Kuczyński1985/86 simultaneous worst Lanczos residual conjecture is precise but no recent explicit reaffirmation found; source is a scanned report and was not fully inspected.
- Block Gram–Schmidt conjectures in Carson–Lund–Rozložník–Thomas2022 have substantial later resolutions by Zou2025 and Carson–Lund–Ma–Oktay2026. Not recycled without exact algorithm reconciliation.
- Hashemi–Nakatsukasa Sherman–Morrison iterative-refinement conjecture was sent to the functions/stability search for independent assessment.
- The 1997 collocation paper also conjectures positivity of all leading principal minors; no status audit done, so it is not proposed as an additional entry.
