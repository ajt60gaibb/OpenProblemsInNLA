# Finite net contract and preimplementation review

Root proposed, and /root/source_statement_author independently approved, before
implementation: every subset S of the closed unit ball in a finite-dimensional
real normed space has a finite internal half-net with at most5^dim points.
Empty S and dimension0 are included. Scale a half-separated finite subset by2,
apply Mathlib Besicovitch.card_le_of_separated, and take a maximum-cardinality
separated subset. No closedness of S is required. Also prove the exact standard
net consequence: if ||A y||<=B at all net points covering the unit sphere, B>=0,
then the actual continuous linear operator norm satisfies ||A||<=2B.
