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
