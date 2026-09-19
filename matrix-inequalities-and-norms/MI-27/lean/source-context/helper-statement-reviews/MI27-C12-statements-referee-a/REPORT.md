# MI27 C12: independent pre-body statement review

Verdict: APPROVE all nine exact helper headers and their stated assembly into the unchanged frozen C12. No blocking mathematical or statement-fidelity finding.

Reviewer `/root/nr04_mf14_final_referee_a` is a nonauthor of this C12 packet and has written no C12 proof or header. I separately author MI27 C11, so this is an independent review of the new C12 component, not a wholly nonauthor final review of all MI27. I ran no Lean, Lake, or Comparator, edited no C12 source, and certify no implementation or run.

The reviewed exact plan SHA256 is 0dfdccc245cc3dae033c924a695e1dbc7610ab87fcd19c6d1acdb64da27e58ae. The reproduced weighted_entropy_finite_kernel header matches the frozen Challenge after whitespace normalization, including original R, both Loewner bounds, positive a,b with a+b=1, literal scalar kernels, actual chi, and interval integrability. The semantic Definitions remain unchanged.

The mixture strict-density lemma follows from positive scalar sums of positive-definite matrices and complex trace linearity. The chi identity is valid even for arbitrary matrices and arbitrary real a,b: expansion of M=a*rho+b*sigma on the left of log(M) gives the weighted sum of the two relative entropies. No commutation or matrix-log derivative is used, so omitted positivity assumptions there are intentional and sound.

The two hockey-stick mixture identities are exact scalar linear-combination identities followed by nonnegative positive-part homogeneity. With d=b+a*gamma, rho-(gamma/d)M=(b/d)(rho-gamma*sigma); d>0 follows from a,b>0 and gamma>=1, without needing a+b=1. Also M-(a+b*gamma)rho=b(sigma-gamma*rho), valid for every a,gamma when b>=0, including b=0 and singular or repeated spectra.

With a+b=1 and R>=1, d(R)=1+a(R-1) lies in [1,R]. L=R/d(R) is therefore in [1,R]; more directly L>=1 is b(R-1)>=0 and L<=R is d(R)>=1. U=a+bR=1+b(R-1) also lies in [1,R]. The inequality rho<=L*M is equivalent after multiplication by d(R)>0 to b*rho<=b*R*sigma, and M<=U*rho follows from b*sigma<=b*R*rho. Thus the original common R also bounds the pair (rho,M), with no stronger supplied cutoff premise.

Truncation at L and U separately is necessary and correctly placed before substitution. Continuous integrability on the full compact interval and zero above the smaller endpoint justify the truncation lemma, including L=R=1. The forward map gamma/(b+a*gamma) has derivative b/(b+a*gamma)^2, maps 1 to 1 and R to L, and is strictly increasing on [1,R] with positive denominator. The reverse map a+b*gamma has derivative b and endpoints 1,U. Its generic substitution header correctly does not require a>0: b>0 and a+b=1 still give 1+b*(gamma-1)>=1 on the interval. Both change-of-variable formulas include the degenerate R=1 case without a limit.

For D(rho||M), the forward transformed integrand is b^2 E(gamma,rho,sigma)/(gamma*(b+a*gamma)^2), and the reverse is b^2 E(gamma,sigma,rho)/(a+b*gamma)^2, exactly as stated. Swapping (rho,a) with (sigma,b) gives D(sigma||M). Multiplication by a,b yields for E(gamma,rho,sigma) the coefficient (a*b^2/gamma+b*a^2)/(b+a*gamma)^2=a*b/(gamma*(b+a*gamma)); the other is (a*b^2+b*a^2/gamma)/(a+b*gamma)^2=a*b/(gamma*(a+b*gamma)). These are precisely the frozen kernelAB and kernelBA. All denominators are positive on [1,R].

The plan uses C11 only as an internal proved dependency; it introduces no assumed integral identity or replacement entropy. The current absence of a completed compiled C11 is an implementation dependency, not a flaw in these exact mathematical statements. Repeated eigenvalues and noncommuting inputs remain allowed. Empty dimensions are not excluded in the elementary helpers; the density premises and frozen n>=1 are handled as stated.

Approval is limited to statements and the mathematical route before proof bodies. Actual root-controlled local compilation, permitted-axiom audits, final independent proof review, exact elaborated contract checks, and Linux Comparator remain separate obligations. No completed original target or count increment is claimed.
