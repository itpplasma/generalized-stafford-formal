module

public import GeneralizedStafford.ProjectiveWidth.Generation
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-! # Exactness and finite rank for right Ore localization -/

namespace GeneralizedStafford.ProjectiveWidth

open MulOpposite Submodule OreLocalization
open scoped nonZeroDivisors

variable {A : Type*} [Ring A] [IsDomain A] [OreSet (Aᵐᵒᵖ)⁰]
variable {M N : Type*} [AddCommGroup M] [Module Aᵐᵒᵖ M]
    [AddCommGroup N] [Module Aᵐᵒᵖ N]

omit [IsDomain A] in
/-- Ore localization preserves surjections. -/
theorem locMap_surjective (f : M →ₗ[Aᵐᵒᵖ] N) (hf : Function.Surjective f) :
    Function.Surjective (locMap (Λ := A) f) := by
  intro z
  induction z using OreLocalization.ind with
  | c n s =>
    obtain ⟨m, rfl⟩ := hf n
    exact ⟨m /ₒ s, locMap_oreDiv f m s⟩

/-- Exactness at a localized module for the quotient by any submodule. -/
theorem locMap_mkQ_ker (W : Submodule Aᵐᵒᵖ M) :
    LinearMap.ker (locMap (Λ := A) W.mkQ) =
      LinearMap.range (locMap (Λ := A) W.subtype) := by
  apply le_antisymm
  · intro z hz
    induction z using OreLocalization.ind with
    | c m s =>
      change locMap (Λ := A) W.mkQ (m /ₒ s) = 0 at hz
      rw [locMap_oreDiv, ← zero_oreDiv s, oreDiv_eq_iff] at hz
      obtain ⟨u, v, h1, h2⟩ := hz
      have he : (u : Aᵐᵒᵖ) = v := mul_right_cancel₀ (nonZeroDivisors.coe_ne_zero s) h2
      have hm : (u : Aᵐᵒᵖ) • m ∈ W := by
        rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_smul, he]
        simpa only [smul_zero] using h1.symm
      refine ⟨(⟨(u : Aᵐᵒᵖ) • m, hm⟩ : W) /ₒ (u * s), ?_⟩
      rw [locMap_oreDiv]
      exact (OreLocalization.expand' m s u).symm
  · rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    induction z using OreLocalization.ind with
    | c w s =>
      rw [locMap_oreDiv, locMap_oreDiv, Submodule.subtype_apply,
        show W.mkQ (w : M) = 0 from (Submodule.Quotient.mk_eq_zero _).mpr w.property,
        zero_oreDiv]

/-- The rank of a submodule and its quotient add to the ambient Ore rank. -/
theorem oreRank_quotient_add [Module.Finite Aᵐᵒᵖ M] (W : Submodule Aᵐᵒᵖ M) :
    oreRank A (M ⧸ W) + oreRank A W = oreRank A M := by
  have := finite_loc (Λ := A) (M := M)
  have hsurj := locMap_surjective W.mkQ W.mkQ_surjective
  have hker := locMap_mkQ_ker W
  have hrange := LinearMap.range_eq_top.mpr hsurj
  have hdim := (locMap (Λ := A) W.mkQ).finrank_range_add_finrank_ker
  rw [hrange, finrank_top, hker,
    LinearMap.finrank_range_of_inj (locMap_injective W.injective_subtype)] at hdim
  exact hdim

/-- Localizing the image of a map gives the image of its localized map. -/
theorem locMap_range (f : M →ₗ[Aᵐᵒᵖ] N) :
    LinearMap.range (locMap (Λ := A) f) =
      LinearMap.range (locMap (Λ := A) (LinearMap.range f).subtype) := by
  have he : f = (LinearMap.range f).subtype.comp f.rangeRestrict := rfl
  conv_lhs => rw [he, locMap_comp]
  rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr
    (locMap_surjective f.rangeRestrict (LinearMap.range_eq_top.mp f.range_rangeRestrict)),
    Submodule.map_top]

/-- Image rank agrees with dimension of the image in the fraction module. -/
theorem oreRank_range (f : M →ₗ[Aᵐᵒᵖ] N) :
    oreRank A (LinearMap.range f) =
      Module.finrank (QΛ A) (LinearMap.range (locMap (Λ := A) f)) := by
  rw [locMap_range, LinearMap.finrank_range_of_inj
    (locMap_injective (LinearMap.range f).injective_subtype)]
  rfl

/-- Choose integral columns of a map whose localized images are independent
and whose number is exactly its localized image rank. -/
theorem independent_image_columns [Module.Finite Aᵐᵒᵖ M]
    (f : M →ₗ[Aᵐᵒᵖ] N) :
    ∃ E : (Fin (oreRank A (LinearMap.range f)) → A) →ₗ[Aᵐᵒᵖ] M,
      LinearIndependent (QΛ A)
        (fun j => toLoc A N (f (E (Pi.single j 1)))) := by
  classical
  have := finite_loc (Λ := A) (M := LinearMap.range f)
  obtain ⟨κ, x, _, hspan, hx⟩ := exists_linearIndependent' (QΛ A)
    (toLoc A (LinearMap.range f))
  let b := Module.Basis.mk hx (by rw [hspan, span_range_toLoc])
  have : Finite κ := Module.Finite.finite_basis b
  let := Fintype.ofFinite κ
  have hcard : Fintype.card κ = oreRank A (LinearMap.range f) :=
    (Module.finrank_eq_card_basis b).symm
  let e := (Fintype.equivFinOfCardEq hcard).symm
  choose p hp using fun j : Fin (oreRank A (LinearMap.range f)) => (x (e j)).property
  refine ⟨combo p, ?_⟩
  have hmap := hx.map' (locMap (Λ := A) (LinearMap.range f).subtype)
    (LinearMap.ker_eq_bot.mpr (locMap_injective (LinearMap.range f).injective_subtype))
  have hli := hmap.comp e e.injective
  convert hli using 1
  funext j
  simp only [Function.comp_apply, locMap_toLoc, Submodule.subtype_apply]
  congr 1
  have he : combo (Λ := A) p (Pi.single j 1) = p j := by
    simp [combo_apply, Pi.single_apply, apply_ite]
  rw [he, hp]

/-- A zero right module has zero Ore rank. -/
theorem oreRank_subsingleton [Subsingleton M] : oreRank A M = 0 := by
  have hz : ∀ z : Loc A M, z = 0 := by
    intro z
    induction z using OreLocalization.ind with
    | c m s => rw [Subsingleton.elim m 0, zero_oreDiv]
  have : Subsingleton (Loc A M) := ⟨fun x y => (hz x).trans (hz y).symm⟩
  exact Module.finrank_zero_of_subsingleton

/-- The free right module `A^n` has Ore rank `n`. -/
theorem oreRank_free (n : ℕ) : oreRank A (Fin n → A) = n := by
  induction n with
  | zero => exact oreRank_subsingleton
  | succ n ih =>
    let e : (Fin (n + 1) → A) ≃ₗ[Aᵐᵒᵖ] A × (Fin n → A) :=
      { toFun := fun f => (f 0, Fin.tail f)
        invFun := fun p => Fin.cons p.1 p.2
        left_inv := fun f => by funext i; exact Fin.cases rfl (fun _ => rfl) i
        right_inv := fun p => by cases p; rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    rw [oreRank_eq_of_equiv e, oreRank_prod, oreRank_self, ih]
    omega

end GeneralizedStafford.ProjectiveWidth
