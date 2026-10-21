module

public import AlgebraicAnalysis.Module.ColonSupport
public import AlgebraicAnalysis.Module.DeviationOmega
public import AlgebraicAnalysis.Ore.Noetherian

@[expose] public section

/-!
# Fixed-anchor recursion and finite deviation

The right ideals and the mixed-anchor colon maps are upstream declarations.
These lemmas specialize their Serre predicate to actual finite module deviation
and implement the ordered substitutions in `docs/fixed-anchor-gluing.md`, §3.
They do not assert the dimension-lowering pencil step.
-/

namespace GeneralizedStafford.FixedAnchor

open AlgebraicAnalysis AlgebraicAnalysis.DenominatorTorsion
open AlgebraicAnalysis.ColonSupport

universe u
variable {R : Type u} [Ring R]

/-- The strict finite deviation stratum is a Serre predicate, including the
zero-module convention at level zero. -/
theorem small_serre (e : ℕ) :
    IsSerreClosed (R := R) (fun M => Module.Small Rᵐᵒᵖ e M) where
  of_injective f hf h := h.of_injective f hf
  of_surjective f hf h := h.of_surjective f hf
  of_exact i p hi hp hip hA hC :=
    (Module.small_iff_of_exact e i p hi hp hip).mpr ⟨hA, hC⟩

/-- The mixed-anchor bound at a strict deviation stratum. -/
theorem refined_small (e : ℕ) (d f g L C : R) (h : f * d * L = d * C)
    (hI : Module.Small Rᵐᵒᵖ e (R ⧸ firstIdeal d f))
    (hQ : Module.Small Rᵐᵒᵖ e (R ⧸ secondIdeal d g L)) :
    Module.Small Rᵐᵒᵖ e (R ⧸ refinedIdeal d f g) :=
  refinedIdeal_quotient_mem _ (small_serre e) d f g L C h hI hQ

/-- In particular, two bounded quotients give the same bound for the colon
refinement; the principal anchor is still `d`. -/
theorem refined_devLE (n : ℕ) (d f g L C : R) (h : f * d * L = d * C)
    (hI : Module.DevLE Rᵐᵒᵖ n (R ⧸ firstIdeal d f))
    (hQ : Module.DevLE Rᵐᵒᵖ n (R ⧸ secondIdeal d g L)) :
    Module.DevLE Rᵐᵒᵖ n (R ⧸ refinedIdeal d f g) :=
  refined_small (n + 1) d f g L C h hI hQ

/-- Every ideal containing the fixed principal anchor inherits its finite
quotient bound. -/
theorem quotient_devLE {n : ℕ} {d : R}
    (hd : Module.DevLE Rᵐᵒᵖ n (R ⧸ anchor d))
    (X : Submodule Rᵐᵒᵖ R) (hX : anchor d ≤ X) :
    Module.DevLE Rᵐᵒᵖ n (R ⧸ X) :=
  hd.of_surjective (Submodule.factor hX) (Submodule.factor_surjective hX)

/-- The exact fixed-anchor recursive choices. In particular, the second
recursive ideal is `dR + (H₂ a')dR = dR + (H₂ a)dLR`, without changing `d`. -/
theorem recursion_data [IsDomain R] [IsNoetherian Rᵐᵒᵖ R]
    {d a : R} (hd : d ≠ 0) (ha : a ≠ 0) (f : R) :
    ∃ T C₀ : R, T ≠ 0 ∧ f * d * T = d * C₀ ∧
      let L := T * a * d
      let C := C₀ * a * d
      let a' := a * d * T * a
      L ≠ 0 ∧ a' ≠ 0 ∧ f * d * L = d * C ∧
        ∀ H₂ : R, (H₂ * a') * d = (H₂ * a) * d * L ∧
          firstIdeal d (H₂ * a') = secondIdeal d (H₂ * a) L := by
  have hOre := OreRightIntersection.rightOreCondition_of_isNoetherian (R := R)
  have hden : ∃ T C₀ : R, T ≠ 0 ∧ f * d * T = d * C₀ := by
    by_cases hf : f = 0
    · exact ⟨1, 0, one_ne_zero, by simp [hf]⟩
    obtain ⟨T, C₀, he, hne⟩ := hOre (mul_ne_zero hf hd) hd
    exact ⟨T, C₀, fun hz => hne (by simp [hz]), he⟩
  obtain ⟨T, C₀, hT, he⟩ := hden
  refine ⟨T, C₀, hT, he, mul_ne_zero (mul_ne_zero hT ha) hd,
    mul_ne_zero (mul_ne_zero (mul_ne_zero ha hd) hT) ha, ?_, ?_⟩
  · simp only [← mul_assoc, he]
  · intro H₂
    have hmul : H₂ * (a * d * T * a) * d = H₂ * a * d * (T * a * d) := by
      simp only [mul_assoc]
    exact ⟨hmul, by simp only [firstIdeal, secondIdeal, hmul]⟩

/-- The central pencil correction stays in the prescribed right affine coset. -/
theorem affine_update (B H H₂ a lam : R) :
    (B + H * a) + lam * (H₂ * a) = B + (H + lam * H₂) * a := by
  simp only [add_mul, mul_assoc, add_assoc]

/-- Detection at level zero supplies the actual integral coefficients. -/
theorem coefficients_of_small_zero (d f : R)
    (h : Module.Small Rᵐᵒᵖ 0 (R ⧸ firstIdeal d f)) :
    ∃ U V : R, 1 = d * U + f * d * V := by
  have hz : (firstIdeal d f).mkQ 1 = 0 := h.elim _ _
  have hm : (1 : R) ∈ firstIdeal d f := (Submodule.Quotient.mk_eq_zero _).mp hz
  obtain ⟨x, ⟨U, rfl⟩, y, ⟨V, rfl⟩, he⟩ := Submodule.mem_sup.mp hm
  exact ⟨U, V, he.symm⟩

/-- The upstream omega bound supplies the finite principal quotient input.
This is a reduction of the omega corollary, not an S1 producer. -/
theorem principal_quotient_finite_of_omega [IsDomain R]
    (hR : Module.DevLEOmega Rᵐᵒᵖ R) {d : R} (hd : d ≠ 0) :
    ∃ n, Module.DevLE Rᵐᵒᵖ n (R ⧸ anchor d) := by
  have he : LinearMap.mulLeft Rᵐᵒᵖ d = leftMulLinear d := by ext; rfl
  change ∃ n, Module.DevLE Rᵐᵒᵖ n (R ⧸ (leftMulLinear d).range)
  rw [← he]
  exact hR.principal_right_quotient hd

end GeneralizedStafford.FixedAnchor
