/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted aggregate by /root/pf03_final_referee2.

NR-04 candidate complete implementation of the unchanged original target.
Mathematical source: Matthew J. Colbrook, University of Cambridge; reflection
upper-bound attribution to Hrubeš / Gillis--Glineur remains in the manuscript.
This module imports actual proofs independently from the shared Definitions.
It neither imports nor depends on the deliberately incomplete Challenge.
All fifteen frozen contracts are exposed and audited below. Compiler, external
Comparator and independent-referee status must be reported from actual receipts.
-/
import NLA.NR04.FinalBounds

set_option autoImplicit false
set_option leancert.trust "kernel"

#print axioms NLA.NR04.minor_eight_positive
#print axioms NLA.NR04.distance_index_semantics
#print axioms NLA.NR04.centered_labels
#print axioms NLA.NR04.reflection_identity
#print axioms NLA.NR04.seven_factor_certificate
#print axioms NLA.NR04.distance_rank_certificate
#print axioms NLA.NR04.distance_sign_pattern
#print axioms NLA.NR04.small_section_bound
#print axioms NLA.NR04.section_contact_bound
#print axioms NLA.NR04.low_rank_factor_obstruction
#print axioms NLA.NR04.rank_three_small_factor
#print axioms NLA.NR04.general_rank_seven_lower
#print axioms NLA.NR04.nine_point_no_small_factor
#print axioms NLA.NR04.nine_point_nonnegative_rank_seven
#print axioms NLA.NR04.canonical_six_factor_impossible

#assert_trust kernel NLA.NR04.minor_eight_positive
#assert_trust kernel NLA.NR04.distance_index_semantics
#assert_trust kernel NLA.NR04.centered_labels
#assert_trust kernel NLA.NR04.reflection_identity
#assert_trust kernel NLA.NR04.seven_factor_certificate
#assert_trust kernel NLA.NR04.distance_rank_certificate
#assert_trust kernel NLA.NR04.distance_sign_pattern
#assert_trust kernel NLA.NR04.small_section_bound
#assert_trust kernel NLA.NR04.section_contact_bound
#assert_trust kernel NLA.NR04.low_rank_factor_obstruction
#assert_trust kernel NLA.NR04.rank_three_small_factor
#assert_trust kernel NLA.NR04.general_rank_seven_lower
#assert_trust kernel NLA.NR04.nine_point_no_small_factor
#assert_trust kernel NLA.NR04.nine_point_nonnegative_rank_seven
#assert_trust kernel NLA.NR04.canonical_six_factor_impossible
