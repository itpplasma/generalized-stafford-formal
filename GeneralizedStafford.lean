module

/-
Adapted from itpplasma/symplectic-stafford-formal, revision
0e55a8059cc923ef39d6ddb66c5b6f6a2682b46b. Modified 21 October 2026:
generalized filtration hypotheses and migrated to GeneralizedStafford.
Original manuscript section references are retained for correspondence.
-/

public import GeneralizedStafford.Setting
public import GeneralizedStafford.RightFraction
public import GeneralizedStafford.Localization
public import GeneralizedStafford.Pencil
public import GeneralizedStafford.DivisionPencil
public import GeneralizedStafford.NoFiniteRank
public import GeneralizedStafford.Test
public import GeneralizedStafford.SourceSelection
public import GeneralizedStafford.Dimension
public import GeneralizedStafford.Induction
public import GeneralizedStafford.Opposite
public import GeneralizedStafford.ConsequencesGeneration
public import GeneralizedStafford.ConsequencesRank
public import GeneralizedStafford.ConsequencesForU
public import GeneralizedStafford.Main
public import GeneralizedStafford.ProjectiveWidth.Matrix

@[expose] public section

/-!
# The general filtered Stafford theorem

This umbrella module imports the generalized Mathlib-only development: the filtered setting and localization package (§§2–3 with the
Zariskian closure Z1–Z9), finite-length source selection and pencils (§4),
the common colon ideal and the controlled codimension induction (§§5–6),
opposite transport and the module-theoretic consequences (§7).  The main
theorem is `GeneralizedStafford.FilteredAlgebraData.targetA`. The conditional
projective and matrix affine width theorems are exported from `ProjectiveWidth`;
their scalar S1 and bilateral Ore hypotheses remain explicit.
-/
