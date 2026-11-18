module

import MT
import Solution

/-! Print axioms in the solution environment. The separate tower check is in
    checks/TowerAxioms.lean. -/

-- The surface, admissible tests and the core-to-full implication
#print axioms MT.localConstant_mono
#print axioms MT.localConstant_le_full
#print axioms MT.full_lower_bound_iff_integrable
#print axioms MT.GraphChart.local_area_bounds
#print axioms MT.HasCurvature.exists_parabolic_slice
#print axioms MT.GraphChart.exists_taylor_bound

-- Witness estimates and unconditional proof of Proposition 3.1
#print axioms MT.analyticTransfer
#print axioms MT.fourier_tent
#print axioms MT.tent_large_sieve
#print axioms MT.counterWeight_line_bound
#print axioms MT.counterWeight_xrayNorm
#print axioms MT.counterWeight_xrayNorm_pos
#print axioms MT.admissible_counterWeight
#print axioms MT.resonant_patch_mass
#print axioms MT.product_tent_kernel
#print axioms MT.packet_energy_expansion
#print axioms MT.packet_kernel_identity
#print axioms MT.packet_mass_ge_energy
#print axioms MT.cap_weightedMass_lower
#print axioms MT.GraphChart.cap_test_data
#print axioms MT.counterWeight_at_transfer_scale
#print axioms MT.localConstant_of_transfer_estimates

-- Arithmetic estimates and the finite sets
#print axioms MT.Seed.exists_bounded_seed
#print axioms MT.Seed.exists_seed_energy
#print axioms MT.Seed.exists_seed_rectangles
#print axioms MT.Seed.card_overlap_labels
#print axioms MT.Seed.returning_rectangle
#print axioms MT.Arithmetic.configuration_of_bounded_field_sets
#print axioms MT.choose_seed_size
#print axioms MT.Arithmetic.configuration_of_field_bounds
#print axioms MT.Seed.field_line_count
#print axioms MT.TracePairing.inner_embedding
#print axioms MT.Arithmetic.minkowski_covolume
#print axioms MT.Arithmetic.mem_minkowski_dual_iff
#print axioms MT.Arithmetic.minkowski_dual_coordinate_gap
#print axioms DedekindZeta.PoissonSummation.tsum_eq_tsum_fourier
#print axioms MT.lattice_count_of_fourier_tail
#print axioms MT.BoxCutoff.lattice_box_lower
#print axioms MT.BoxCutoff.lattice_box_upper
#print axioms MT.Arithmetic.one_le_abs_rational_norm
#print axioms MT.Arithmetic.conjugate_gap
#print axioms MT.Arithmetic.dual_product_gap
#print axioms MT.Arithmetic.normalized_integral_gap
#print axioms MT.Arithmetic.projected_strip_card_le
#print axioms MT.BoxCounting.remainder_bound
#print axioms MT.BoxCounting.count_of_poisson_and_decay
#print axioms MT.Arithmetic.fieldRect_lower
#print axioms MT.Arithmetic.fieldBox_uniform
#print axioms MT.Seed.exists_overlap_scale
#print axioms MT.Intersections.card_return_lower
#print axioms MT.Intersections.field_intersection_estimates
#print axioms MT.arithmeticAmplification_of_dyadic_fields
#print axioms MT.energy_of_return_proportion
#print axioms MT.project_preserves_counts
#print axioms MT.arithmeticAmplification_of_tail

-- Section 5 (both proposition inputs are explicit)
#print axioms MT.paperExponent_pos
#print axioms MT.powerLoss_of_dyadic_samples
#print axioms MT.powerLoss_of_transfer_and_amplification

-- The tower, arithmetic amplification, and the unconditional target
#print axioms MT.Tower.dyadic_totally_real_fields
#print axioms MT.arithmeticAmplification
#print axioms MT.powerlossMT
