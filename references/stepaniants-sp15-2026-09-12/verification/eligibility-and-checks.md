# SP-15: eligibility and verification record

Checked on 12 September 2026 UTC. This is a private research record, not a publication or a claim of exhaustive novelty.

## Canonical target

The exact canonical source was read from `refs/remotes/upstream/main` at commit `1f22006bdaa4659fcaa0bb775a887685cd3cc566`, path `eigenvalues-and-inverse-problems/SP-15/README.md`, and archived as `canonical-statement.md`. It is Partially resolved and asks for a finite, dimension-dependent uniform bound on unitary similarity classes in **every** complete shifted-singular-value fiber of complex matrices. It has no nonderogatory or simple-spectrum assumption. An infinite fiber at order nine therefore disproves the full universal statement.

## Primary and later-literature scope

The primary 2009 source is Fortier Bourque–Ransford, *Super-identical pseudospectra*, JLMS79(2),511–528, DOI https://doi.org/10.1112/jlms/jdn085 . The source's Section6.2 asks whether Theorem1.4 holds with empty exceptional set; this section was checked in indexed primary text. An attempt to open the full author manuscript URL through the web tool failed. This access limitation does not affect the separate full published 2010 primary source check.

The complete published 2010 primary survey was opened and its Theorem5.4 and discussion on printed pp336–337 inspected directly:
https://www.impan.pl/shop/en/publication/transaction/download/product/86371 . It states generic finiteness up to a closed measure-zero exceptional set and explicitly leaves removal of the exceptional set open. Its invariant-theory discussion about algebraicity and failure of integrality is distinct from the present real positive-definite construction.

The 2012 Armentia–Gracia–Velasco primary accepted manuscript was checked for its exact ordinary-similarity scope, using:
https://addi.ehu.es/bitstream/handle/10810/70520/IdenticalPseudospectraOfAnyGeometricMultiplicity-1.pdf?isAllowed=y&sequence=6 . Its conclusion is compatible with the proposed family's fixed Jordan type (3,3,3).

The Ransford–Walsh 2022 primary paper was read during the immediately preceding MF-24 pass, including its current arXiv v2 and published scope; it concerns norm-comparison and similarity-conditioning bounds, not finiteness of exceptional fibers. Primary version: https://arxiv.org/pdf/2109.14472v2 ; publication https://doi.org/10.1007/s11117-022-00928-8 . No result from that paper is required by the proposed proof.

Bounded current searches included the exact phrase “super-identical pseudospectra” combined with “finite unitary”, “nilpotent infinite”, “exceptional”, “continuous”, “finiteness”, “unitary2025”, and “exceptional2024”. Results yielded the original papers, the 2022 norm paper and unrelated listings. A 2024-indexed Oxford meeting page is about a 2009 workshop, so it was not treated as a new 2024 theorem. No later full resolution was found. This is a bounded literature check, not proof of novelty.

## Public network

`network_check.py` is a read-only GitHub API audit. It recursively enumerated all returned public forks of the source repository and read every public branch head. The snapshot `public-network.json` completed at **2026-09-12T00:54:41.638822+00:00**:

- 5 public repositories;
- 37 branch heads;
- 98 distinct selected text blobs (canonical target, root indexes, ID-named and relevant super-identical/pseudospectrum/unitary-named text);
- 32 PR review bodies, in addition to issues, PR bodies, issue comments and inline PR comments.

SP-15 was present and Partially resolved on 8 branch heads, and absent on 29 older heads. The only matching discussion was upstream PR111, which introduced the permanent target and recorded it as an active partially resolved entry. It is not a solution submission. No full solution was found in the checked public material.

The raw snapshot is private. `network-check-sanitized.json` removes all file contents and discussion bodies while retaining repository/branch paths, status, blob/content hashes and the exact PR111 match disposition. The scope does not include private, deleted, unpublished or unidentifiably named work, or assert access to any separate discussion surface that was not returned by these issue/PR API endpoints.

## Proof and diagnostics

The frozen proof candidate is `RESULT.md`, 9,440 bytes, SHA256 `d992da0546924d7fbc9f1bb0e89e00b1442ec3c3045c739722c9767078ce40c1`. Its main proof is analytic: block Schur complements, a polynomial coefficient count, an explicit phase gauge for unitary classes, and the smooth constant-rank theorem.

`check_identity.py` separately checks the determinant identity at five exact integer test cases, including complex shifts. It uses integer realification and fraction-free Bareiss determinants. These diagnostic checks passed. Their finite number is explicitly not a proof of the quantified identity or an explicit construction of the constant-rank fiber. The file `identity-check.json` retains every input and exact integer output.

No unitary-class count or positive-dimensional-fiber assertion is based on floating-point optimization. No canonical file, repository status, commit, push, issue or pull request was changed by this research pass. Independent review is still required before any submission labels the target solved.
