# Independent review of the append right inverse

Root read the complete source by /root/infrastructure and independently
compiled SHA-256
`ad5a57ca9de31d712d274529f09758578fc1a8f15435102e572265960f9bba96`.
All sixteen kernel assertions passed, with only propext, Classical.choice,
and Quot.sound and no warnings.

The actual Moore-Penrose inverse is compared with any genuine right inverse
by its Hermitian idempotent projection, giving both operator and Frobenius
inequalities. Canonical Fin-indexed horizontal and vertical concatenation
are proved to satisfy the required matrix identities. The explicit append
witness uses the fixed retained R and discarded U, and multiplication gives
the identity from MR=I-UU^T and (U^T G)P=I. The Frobenius cross term is
exactly zero from RU=0. Column-count bounds introduce k rather than n.
The final bounds are precisely 2||R||^2+4(1+||RG||^2)||P||^2 and
||R||_F^2+k(1+||RG||^2)||P||^2. Empty dimensions remain covered.

Approved exact statements and proofs; probability and scalar absorption
belong to the separate Gaussian append theorem.
