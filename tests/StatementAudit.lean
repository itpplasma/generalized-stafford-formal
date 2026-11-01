module

import GeneralizedStafford

open GeneralizedStafford

-- Print the actual data and theorem type, including every ambient assumption.
#print FilteredAlgebraData
#print Statement
#check @FilteredAlgebraData.targetA
#check @FilteredAlgebraData.targetA_left
#check @FilteredAlgebraData.targetA_left_affine
#check @universalStatement

-- Conditional width uses the existing scalar S38 property and actual Ore rank.
#print ProjectiveWidth.S1
#print ProjectiveWidth.AffineAnchoredIdentity
#print ProjectiveWidth.localizedImageRank
#print ProjectiveWidth.matrixOreRank
#check @ProjectiveWidth.prescribed_generators
#check @ProjectiveWidth.projective_anchored_width
#check @ProjectiveWidth.matrix_anchored_width
#check @ProjectiveWidth.matrix_rank_two_three

-- Actual-germ fixed-anchor endpoints, including finite descent and omega S1.
#check @FixedAnchor.recursion_data
#check @FixedAnchor.exists_affine_germ_tests
#check @FixedAnchor.exists_affine_epic_tests
#check @FixedAnchor.exists_affine_small_with_tests
#check @FixedAnchor.affine_of_devLE_zero
#check @FixedAnchor.activated_germ_pencil_finite
#check @FixedAnchor.affine_of_devLE_one
#check @FixedAnchor.torsion_cyclic_of_devLE_one
#print FixedAnchor.EpicGermTest
#print FixedAnchor.AffineBound
#check @FixedAnchor.secondCallPair_epic
#check @FixedAnchor.secondCall_vL_zero
#check @FixedAnchor.secondCall_joint_injective
#check @FixedAnchor.secondCall_pencil_finite
#check @FixedAnchor.secondCall_small_finite
#check @FixedAnchor.affineBound_step
#check @FixedAnchor.affineBound_descend
#check @FixedAnchor.affine_of_finite_deviation_with_tests
#check @FixedAnchor.affine_of_finite_deviation
#check @FixedAnchor.affine_of_devLE_omega
#check @FixedAnchor.s38_of_devLE_omega
#check @FixedAnchor.torsion_cyclic_of_devLE_omega

-- Theorem A' (fixed ideal), Theorem A by specialization, Corollaries B, C.1, C.2
-- (docs/core-theorem.md at research revision 522b965), domain case.
#print FixedAnchor.IdealBound
#check @FixedAnchor.idealBound_step
#check @FixedAnchor.fixed_ideal_with_tests
#check @FixedAnchor.fixed_ideal
#check @FixedAnchor.fixed_anchor_of_fixed_ideal
#check @FixedAnchor.quotient_finite_of_omega
#check @FixedAnchor.fixed_ideal_of_devLE_omega
#check @FixedAnchor.prescribed_cyclic
#check @FixedAnchor.prescribed_cyclic_of_principal
#check @FixedAnchor.prescribed_cyclic_of_devLE_omega
#check @FixedAnchor.two_generated_of_principal
#check @FixedAnchor.two_generated_of_devLE_omega
#check @FixedAnchor.exists_two_generators_of_principal

-- Input I1 (Goldie) for simple right Noetherian rings, zero divisors allowed:
-- essential right ideals contain regular elements, right Ore condition,
-- Goldie torsion and escape (docs/core-theorem.md §2 and Lemma 3.4).
#print Goldie.IsEssential
#print Goldie.IsGoldieTorsion
#check @Goldie.eq_zero_of_isEssential_rightAnn
#check @Goldie.exists_mem_nonZeroDivisors_of_isEssential
#check @Goldie.exists_right_ore
#check @Goldie.nonempty_oreSet_op
#check @Goldie.exists_mem_nonZeroDivisors_finset
#check @Goldie.isGoldieTorsion_quotient
#check @Goldie.exists_common_regular_annihilator
#check @Goldie.exists_smul_mul_not_mem_of_goldie
#check @Goldie.exists_affine_source_of_goldie
#check @Goldie.section_isGoldieTorsion
