module

public import GeneralizedStafford.FixedAnchor.Descent
public import GeneralizedStafford.ConsequencesGeneration

@[expose] public section

/-!
# Finite fixed-anchor induction and the omega corollary

Starting at `Small (N+1)`, exactly `N+1` applications of the two-call
step reach `Small 0`. Detection then extracts integral right coefficients.
All tests are actual module germs, as in `Descent`.
-/

namespace GeneralizedStafford.FixedAnchor

open Module AlgebraicAnalysis AlgebraicAnalysis.ColonSupport
open AlgebraicAnalysis.DenominatorTorsion

universe u
variable {R : Type u} [Ring R] [IsDomain R] [IsSimpleRing R]
  [IsNoetherian Rᵐᵒᵖ R]
variable {k : Type*} [Field k] [Infinite k] [Algebra k R]
include k

/-- Finite descent lowers the uniform bound by precisely `h` steps. -/
theorem affineBound_descend {d : R} (hd : d ≠ 0) (e h : ℕ) :
    AffineBound d (e + h) → AffineBound d e := by
  induction h with
  | zero => exact fun hb => hb
  | succ h ih =>
    intro hb
    exact ih (affineBound_step (k := k) hd (e + h) hb)

/-- The full fixed-anchor affine identity for a finite-deviation principal
quotient, carrying every finite family of actual epic germ tests. -/
theorem affine_of_finite_deviation_with_tests {N : ℕ} {d a : R}
    (hd : d ≠ 0) (ha : a ≠ 0)
    (hdev : Module.DevLE Rᵐᵒᵖ N (R ⧸ anchor d)) (B : R)
    {ι : Type u} [Fintype ι] (tests : ι → EpicGermTest R) :
    ∃ H U V : R, 1 = d * U + (B + H * a) * d * V ∧
      ∀ i, (tests i).Satisfied (B + H * a) := by
  have hzero := affineBound_descend (k := k) hd 0 (N + 1)
    (by simpa only [Nat.zero_add] using (affineBound_initial (k := k) hdev))
  obtain ⟨H, hsmall, htests⟩ := hzero a ha B tests
  obtain ⟨U, V, hUV⟩ := coefficients_of_small_zero d (B + H * a) hsmall
  exact ⟨H, U, V, hUV, htests⟩

/-- Fixed-anchor affine S1 for a simple right Noetherian domain over an
infinite central field, assuming only a finite bound on `R/dR`. -/
theorem affine_of_finite_deviation {N : ℕ} {d a : R}
    (hd : d ≠ 0) (ha : a ≠ 0)
    (hdev : Module.DevLE Rᵐᵒᵖ N (R ⧸ anchor d)) (B : R) :
    ∃ H U V : R, 1 = d * U + (B + H * a) * d * V := by
  obtain ⟨H, U, V, hUV, _⟩ := affine_of_finite_deviation_with_tests
    (k := k) hd ha hdev B (fun i : PEmpty.{u + 1} => nomatch i)
  exact ⟨H, U, V, hUV⟩

/-- Deviation at most omega supplies the finite principal-quotient input
through `AlgebraicAnalysis.Module.DeviationOmega`. -/
theorem affine_of_devLE_omega (hR : Module.DevLEOmega Rᵐᵒᵖ R)
    {d a : R} (hd : d ≠ 0) (ha : a ≠ 0) (B : R) :
    ∃ H U V : R, 1 = d * U + (B + H * a) * d * V := by
  obtain ⟨N, hN⟩ := principal_quotient_finite_of_omega hR hd
  exact affine_of_finite_deviation (k := k) hd ha hN B

/-- The same-divisor interface under the omega bound. -/
theorem s38_of_devLE_omega (hR : Module.DevLEOmega Rᵐᵒᵖ R) : S38 R := by
  intro d hd
  obtain ⟨H, U, V, he⟩ := affine_of_devLE_omega (k := k) hR hd one_ne_zero 0
  exact ⟨H, U, V, by simpa only [mul_one, zero_add] using he⟩

/-- The existing ordinary torsion cyclicity consequence under the omega bound. -/
theorem torsion_cyclic_of_devLE_omega (hR : Module.DevLEOmega Rᵐᵒᵖ R)
    {M : Type*} [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M]
    (ht : IsTorsionRight (R := R) (M := M)) :
    ∃ z : M, Submodule.span Rᵐᵒᵖ {z} = ⊤ := by
  exact isCyclic_of_forall_isRightTorsion
    (fun _ _ ha hb => OreRightIntersection.rightOreCondition_of_isNoetherian ha hb)
    (s38_of_devLE_omega (k := k) hR) ht

end GeneralizedStafford.FixedAnchor
