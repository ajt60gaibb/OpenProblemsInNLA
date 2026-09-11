# IS-03 independent agent proof review

**Verdict: PASS — complete negative resolution of the exact displayed canonical target.**

**Review date:** 11 September 2026.  
**Reviewer:** separate Codex review agent `/root/review_additional_counterexamples`.  
**Canonical target:** `eigenvalues-and-inverse-problems/IS-03/README.md`, complete problem statement.  
**Original manuscript:** `.cache/colbrook-additional-submission/nla_additional_submission/manuscripts/IS-03-proposed-resolution.md`, read in full.

This review independently checks the mathematical argument and its match to the original conjecture. It is an agent audit, not external human peer review or a formal proof certificate. The reviewer did not edit the manuscript, canonical problem, status metadata, submitted verification script, or remotes.

## Exact reviewed identity

The hash covers the **entire original Markdown manuscript**, including front matter, notices, footnote, and references. Decode the original bytes as UTF-8, replace every CRLF with LF, and encode as UTF-8. Do not strip whitespace, extract a proof block, change a final newline, or otherwise normalize the text. The reviewed file already used LF throughout and had no bare CR characters.

- SHA-256: `548553e2f177da2a2c5135030c6a34fff761d2b9c800b246b7f9a6797e02d45c`
- Original length: 5,068 bytes.
- Normalized UTF-8 length: 5,068 bytes.

The PASS applies to the mathematical argument in that full-file identity against the target read on the review date. It does not automatically extend to later modified proofs or separately generated TeX/PDF artifacts.

## Target and primary-source meaning

The local target quantifies over every real entrywise-nonnegative matrix of every order at least five and requires a nonnegative realization of the normalized characteristic derivative in exactly one smaller order. A counterexample at order seven therefore suffices. Reducibility, repeated eigenvalues, positive trace, and nonreal eigenvalues are all permitted.

The primary source defines realizability in the same order as the list and states Johnson's conjecture without irreducibility or trace restrictions. Its Conjecture 1.1 also explicitly asks for nonnegative moments of critical points, and Conjecture 1.2 asks for their realizability. The noted low-order and trace-zero results are restricted cases, not additional conjecture hypotheses. Thus this example addresses the original unrestricted statement, not merely an overbroad repository paraphrase. See [Hoover–McCormick–Paparella–Thrall, printed p. 2, Conjectures 1.1–1.2](https://arxiv.org/pdf/1712.05454).

## Complete construction and proof checks

### 1. Admissible matrix and characteristic polynomial

The displayed matrix has a scalar block equal to one half, a directed two-cycle permutation block, and a directed four-cycle permutation block, in the claimed order. Every entry is a nonnegative real number. Its order is seven and its trace is one half. For each cycle block, the characteristic polynomial is exactly the corresponding power of z minus one. The determinant of the block diagonal matrix is consequently

\[
p(z)=(z-\tfrac12)(z^2-1)(z^4-1)
=z^7-\tfrac12z^6-z^5+\tfrac12z^4-z^3+\tfrac12z^2+z-\tfrac12.
\]

I checked every coefficient of this product. Direct differentiation and division by seven give

\[
q(z)=z^6-\tfrac37z^5-\tfrac57z^4+\tfrac27z^3
-\tfrac37z^2+\tfrac17z+\tfrac17,
\]

including the positive constant term. It is monic and has the required degree six. No root approximation is needed for either identity.

### 2. Newton identities, multiplicities, and exact arithmetic

The two forms of Newton's identities in the manuscript are correct, including the factor k on the coefficient c_k for k at most six and the absence of that separate term thereafter. They hold for roots counted with algebraic multiplicity; repeated roots of p or q cause no exception.

For q, the coefficient list in descending order below the leading term is

\[
(c_1,c_2,c_3,c_4,c_5,c_6)
=\tfrac17(-3,-5,2,-3,1,1).
\]

Independent exact substitution gives all six displayed initial power sums:

| k | s_k |
|---|---|
| 1 | 3/7 |
| 2 | 79/49 |
| 3 | 48/343 |
| 4 | 6731/2401 |
| 5 | 5213/16807 |
| 6 | 219766/117649 |

For example, the third identity gives

\[
s_3=\tfrac37\tfrac{79}{49}+\tfrac57\tfrac37-\tfrac67
=\tfrac{237+105-294}{343}=\tfrac{48}{343},
\]

so the derivative's positive cubic coefficient has been incorporated with the correct sign. At k = 7, the recurrence reads

\[
7s_7=3s_6+5s_5-2s_4+3s_3-s_2-s_1.
\]

Expressing these six terms over 117649 yields the numerators

\[
659298,\quad182455,\quad-659638,\quad49392,\quad-189679,\quad-50421.
\]

Their sum is -8593. Dividing by the additional factor seven gives exactly

\[
s_7=-\frac{8593}{823543}<0.
\]

Every value and sign in manuscript equations (2)–(7) passes.

### 3. Obstruction to every candidate realizing matrix

Suppose any real nonnegative matrix B of order six had characteristic polynomial q. Over the complex numbers it has an upper triangular form with the roots of q, including multiplicities, on the diagonal. The seventh power of an upper triangular matrix has the corresponding seventh powers on its diagonal, and trace is invariant under similarity. Therefore

\[
\operatorname{tr}(B^7)=\sum_{j=1}^{6}\mu_j^7=s_7.
\]

This argument covers defective matrices; diagonalizability is not required. Conversely, matrix multiplication of entrywise-nonnegative matrices preserves entrywise nonnegativity: every entry is a sum of products of nonnegative real entries. Hence every diagonal entry of B^7 is nonnegative and its trace is nonnegative. The exact negative value above is a contradiction. This excludes all candidate matrices of the required order, not just companion matrices or any chosen support pattern.

### 4. Ancillary scope assertions

Appending any finite number of zero eigenvalues leaves the seventh power sum unchanged. The same trace obstruction therefore excludes every realization obtained by zero padding. The manuscript's stronger ancillary statement is valid.

The example does not have trace zero and is not of order at most six, so it does not contradict the source's stated trace-zero low-order results. The argument also disproves the unrestricted Monov moment assertion as stated in the source, although a separate catalog classification of that consequence is outside this task.

## Independent computational cross-check

After inspecting the proof, I wrote a separate standard-library Python calculation using `fractions.Fraction`, without reading or reusing the submitted verification script. It multiplied the three characteristic factors, differentiated the resulting exact coefficients, and generated s_1 through s_7 by Newton's identities. It then independently formed the six-dimensional companion matrix and multiplied that matrix exactly through its seventh power. Every intermediate trace agreed with the corresponding power sum, including

`trace(C^7) = -8593/823543`.

These are supplemental exact arithmetic checks. The contradiction above is the mathematical proof; floating-point eigenvalues or root plots were not used.

## Nonmaterial correction and review limits

There is one bibliographic typo: manuscript reference 2 gives the first author as **C. Hoover**, whereas the linked primary paper lists **Sarah L. Hoover**. The reference should use **S. L. Hoover**. This does not affect the proposition, source identification, or PASS verdict. The original file was left unchanged and the hash above records it with that typo.

No material mathematical gap was found. PASS certifies the full negative answer to the exact universal target within this independent agent audit. It does not establish the smallest possible counterexample order, classify additional assumptions under which realizability survives, assess literature novelty or priority, or claim publication or external human review. The source citation was checked for its actual conjecture and hypotheses; an exhaustive literature search was not performed.
