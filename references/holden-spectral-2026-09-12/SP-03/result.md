# SP-03 — result classification and correspondence

**Author:** Sidney Holden  
**Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation.  
**Submission date:** 12 September 2026.  
**Editorial record:** [Attribution, independent review and scope](../README.md).

The review statements below describe the supplied draft; the linked submission record records subsequent independent review.

**USEFUL REDUCTION / LEMMA.** No generic degree formula is established.

For m>=1, let J=[[0,I_m],[-I_m,0]], let Sp_{2m}(C)={X:X^T JX=J}, and for
Zariski-generic U in C^{2m x 2m} count complex critical points of
f_U(X)=tr((X-U)^T(X-U)). The transpose is bilinear, not a conjugate transpose.
The exact target asks whether D_m=2^{m^2}+2^{2m-1} for **every** m>=1.
Equivalently the critical equation is tr((U-X)^T XH)=0 for every H satisfying
H^T J+JH=0, together with X^T JX=J.

`proof.md` proves a bijective skew-multiplier reduction on the regular locus,
and proves that generic actual critical points avoid the singular denominator.
It obtains a saturated system of m(2m-1) quartics in m(2m-1) variables. It also
rederives D_1=4, already known in the canonical source. No new D_m is counted.

**Status proposal: retain OPEN.** Rephrasing an unsolved all-rank degree count
as an equivalent system is useful but is not a new proved instance of that
count. The known m=1 value does not justify relabeling this entry PARTIAL.
