module

public import GeneralizedStafford.ProjectiveWidth.Generation

@[expose] public section

/-!
# Common integral dual coordinates

All denominators are cleared on the left in `A`, equivalently on the right
in the fraction division ring of `Aᵐᵒᵖ`. This extends the existing
`exists_integral_functional` to a finite family with one common denominator.
-/

namespace GeneralizedStafford.ProjectiveWidth

open MulOpposite Submodule OreLocalization
open scoped nonZeroDivisors

variable {A : Type*} [Ring A] [IsDomain A] [OreSet (Aᵐᵒᵖ)⁰]
variable {P : Type*} [AddCommGroup P] [Module Aᵐᵒᵖ P] [Module.Finite Aᵐᵒᵖ P]

/-- Simultaneously clear a finite family of rational functionals. The common
`d` acts by left multiplication on integral coordinates in `A`. -/
theorem integral_functionals (hL : LeftOre A) {ι : Type*} [Fintype ι]
    (c : ι → Loc A P →ₗ[QΛ A] QΛ A) :
    ∃ d : A, d ≠ 0 ∧ ∃ φ : ι → P →ₗ[Aᵐᵒᵖ] A, ∀ i p,
      numLinear A (op (φ i p)) = c i (toLoc A P p) * numLinear A (op d) := by
  classical
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := Aᵐᵒᵖ) (M := P)
  let F := Finset.univ.biUnion (fun i : ι => G.image (fun p => c i (toLoc A P p)))
  obtain ⟨d, hd⟩ := exists_common_right_denominator hL F
  let g : ι → P →ₗ[Aᵐᵒᵖ] QΛ A := fun i =>
    mulRightLinear (numLinear A (d : Aᵐᵒᵖ)) ∘ₗ
      ((c i).restrictScalars Aᵐᵒᵖ) ∘ₗ toLoc A P
  have hg : ∀ i p, g i p ∈ LinearMap.range (numLinear A) := by
    intro i
    have hle : span Aᵐᵒᵖ (G : Set P) ≤ (LinearMap.range (numLinear A)).comap (g i) := by
      rw [span_le]
      intro p hp
      obtain ⟨v, hv⟩ := hd _ (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ i, Finset.mem_image_of_mem _ hp⟩)
      refine ⟨v, ?_⟩
      rw [numLinear_apply, ← hv]
      change _ = c i (toLoc A P p) * numLinear A (d : Aᵐᵒᵖ)
      rw [numLinear_apply]
    intro p
    rw [hG] at hle
    exact hle mem_top
  let ψ : ι → P →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ := fun i =>
    (LinearEquiv.ofInjective (numLinear A) numLinear_injective).symm.toLinearMap ∘ₗ
      (g i).codRestrict _ (hg i)
  refine ⟨unop (d : Aᵐᵒᵖ), (mem_nonZeroDivisors_op_iff _).mp d.2,
    fun i => (unopLinear A).toLinearMap ∘ₗ ψ i, ?_⟩
  intro i p
  have h : numLinear A (ψ i p) = g i p := by
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.ofInjective_symm_apply]
    rfl
  exact h

/-- An integral dual-coordinate map on any finite family whose localized
images are independent. There is one common nonzero left denominator. -/
theorem dual_denominator (hL : LeftOre A) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → P) (hx : LinearIndependent (QΛ A) (toLoc A P ∘ x)) :
    ∃ c : A, c ≠ 0 ∧ ∃ Z : P →ₗ[Aᵐᵒᵖ] (ι → A),
      ∀ j, Z (x j) = Pi.single j c := by
  classical
  let hs := hx.linearIndepOn_id
  let B := Module.Basis.extend hs
  let p : ι → hs.extend (Set.subset_univ _) := fun i =>
    ⟨toLoc A P (x i), Module.Basis.subset_extend hs ⟨i, rfl⟩⟩
  have hB : ∀ i, B (p i) = toLoc A P (x i) := fun i => Module.Basis.extend_apply_self hs (p i)
  have hp : Function.Injective p := by
    intro i j h
    exact hx.injective (congrArg Subtype.val h)
  obtain ⟨c, hc, φ, hφ⟩ := integral_functionals hL (fun i => B.coord (p i))
  refine ⟨c, hc, LinearMap.pi φ, ?_⟩
  intro j
  ext i
  change φ i (x j) = (Pi.single j c : ι → A) i
  apply op_injective
  apply numLinear_injective (Λ := A)
  rw [hφ, ← hB j, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : j = i
  · subst j
    simp
  · have hpji : p j ≠ p i := fun he => h (hp he)
    simp [hpji, Ne.symm h]

end GeneralizedStafford.ProjectiveWidth
