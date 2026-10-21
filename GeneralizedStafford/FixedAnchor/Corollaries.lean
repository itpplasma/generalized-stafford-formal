module

public import GeneralizedStafford.FixedAnchor.FiniteTop
public import GeneralizedStafford.ConsequencesGeneration

@[expose] public section

/-!
# Complete dimension-one consequences of the fixed-anchor base case

These corollaries use the deviation-zero principal-quotient theorem. They do
not supply the positive-deviation induction or the omega corollary. The written
proof records finite-length S1 as prior to this development.
-/

namespace GeneralizedStafford.FixedAnchor

open AlgebraicAnalysis AlgebraicAnalysis.ColonSupport AlgebraicAnalysis.DenominatorTorsion

universe u
variable {R : Type u} [Ring R] [IsDomain R] [IsSimpleRing R]
  [IsNoetherian Rᵐᵒᵖ R]
variable {k : Type*} [Field k] [Infinite k] [Algebra k R]
include k

/-- Right deviation at most one suffices for affine S1, with no symbol
filtration hypothesis. -/
theorem affine_of_devLE_one (hR : Module.DevLE Rᵐᵒᵖ 1 R)
    {d a : R} (hd : d ≠ 0) (ha : a ≠ 0) (B : R) :
    ∃ H U V : R, 1 = d * U + (B + H * a) * d * V := by
  have he : LinearMap.mulLeft Rᵐᵒᵖ d = leftMulLinear d := by ext; rfl
  have hq : Module.DevLE Rᵐᵒᵖ 0 (R ⧸ anchor d) := by
    change Module.DevLE Rᵐᵒᵖ 0 (R ⧸ (leftMulLinear d).range)
    rw [← he]
    exact (show Module.Small Rᵐᵒᵖ 2 R from hR).principal_right_quotient hd
  exact affine_of_devLE_zero (k := k) hd ha hq B

/-- The existing same-divisor interface supplied by the dimension-one case. -/
theorem s38_of_devLE_one (hR : Module.DevLE Rᵐᵒᵖ 1 R) : S38 R := by
  intro d hd
  obtain ⟨H, U, V, he⟩ := affine_of_devLE_one (k := k) hR hd one_ne_zero 0
  exact ⟨H, U, V, by simpa only [mul_one, zero_add] using he⟩

/-- Finitely generated ordinary torsion modules are cyclic in the complete
dimension-one case, via the existing S38 consequence theorem. -/
theorem torsion_cyclic_of_devLE_one (hR : Module.DevLE Rᵐᵒᵖ 1 R)
    {M : Type*} [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M]
    (ht : IsTorsionRight (R := R) (M := M)) :
    ∃ z : M, Submodule.span Rᵐᵒᵖ {z} = ⊤ := by
  exact isCyclic_of_forall_isRightTorsion
    (fun _ _ ha hb => OreRightIntersection.rightOreCondition_of_isNoetherian ha hb)
    (s38_of_devLE_one (k := k) hR) ht

end GeneralizedStafford.FixedAnchor
