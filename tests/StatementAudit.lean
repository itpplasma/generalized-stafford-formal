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

-- Intrinsic fixed-anchor intermediate endpoints; no positive-deviation S1 is claimed.
#check @FixedAnchor.recursion_data
#check @FixedAnchor.exists_affine_germ_tests
#check @FixedAnchor.exists_affine_epic_tests
#check @FixedAnchor.exists_affine_small_with_tests
#check @FixedAnchor.affine_of_devLE_zero
#check @FixedAnchor.activated_germ_pencil_finite
#check @FixedAnchor.affine_of_devLE_one
#check @FixedAnchor.torsion_cyclic_of_devLE_one
