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
