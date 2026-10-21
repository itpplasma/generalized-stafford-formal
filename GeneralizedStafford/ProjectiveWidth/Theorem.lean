module

public import GeneralizedStafford.ProjectiveWidth.Denominators
public import GeneralizedStafford.ProjectiveWidth.Rank
public import GeneralizedStafford.ProjectiveWidth.Reconstruction

@[expose] public section

/-!
# Conditional affine anchored width

The hypothesis is scalar S1 on a bilateral Ore domain. Rank is measured
in Mathlib's Ore localization, not by an integral splitting assumption.
The proof follows §§1–2 of the research `projective-anchored-width.md`:
prescribed-tail generation, common left denominators, and an integral
projective section.
-/

namespace GeneralizedStafford.ProjectiveWidth

open MulOpposite Submodule
open scoped nonZeroDivisors

variable {A : Type*} [Ring A] [IsDomain A]
    [OreLocalization.OreSet (Aᵐᵒᵖ)⁰]
variable {P : Type*} [AddCommGroup P] [Module Aᵐᵒᵖ P]

/-- **Conditional projective anchored width.** For a finite projective right
module of Ore rank `n` and an endomorphism with localized image rank `r > 0`,
every injective affine tail and every list of `n/r` offsets admit an identity
with exactly `n/r+1` displayed terms. All witnesses are integral.

Scalar S1 and left Ore are hypotheses; right Ore is the Mathlib `OreSet`
instance. No simplicity, Noetherianity, split image, or torsion splitting
is assumed. -/
theorem projective_anchored_width [Module.Finite Aᵐᵒᵖ P]
    [Module.Projective Aᵐᵒᵖ P] (hL : LeftOre A) (hS : S1 A)
    (d a : Module.End Aᵐᵒᵖ P) (ha : Function.Injective a)
    {n r : ℕ} (hn : oreRank A P = n) (hd : localizedImageRank d = r) (hr : 0 < r)
    (B : Fin (n / r) → Module.End Aᵐᵒᵖ P) :
    AffineAnchoredIdentity d a B := by
  classical
  obtain ⟨E, hE⟩ := independent_image_columns d
  have hEa : LinearIndependent (QΛ A)
      (fun j => toLoc A P (a (d (E (Pi.single j 1))))) := by
    have h := hE.map' (locMap (Λ := A) a)
      (LinearMap.ker_eq_bot.mpr (locMap_injective ha))
    convert h using 1
    funext j
    exact (locMap_toLoc a _).symm
  obtain ⟨c, hc, Z, hZ⟩ := dual_denominator hL
    (fun j => a (d (E (Pi.single j 1)))) hEa
  apply reconstruct_of_denominator hS d a B E Z hc hZ
  rw [Fintype.card_fin, Fintype.card_fin]
  have hdim := oreRank_quotient_add (LinearMap.range d)
  have hRank : oreRank A (LinearMap.range d) = r := (oreRank_range d).trans hd
  rw [hRank, hn] at hdim
  rw [hRank]
  have hmod := Nat.mod_lt n hr
  have hdiv := Nat.mod_add_div n r
  nlinarith

/-- The exact free-module statement: `End_A(A^n)` is `M_n(A)` under the
usual column action, and the first left multiplier is fixed to the identity. -/
theorem free_anchored_width (hL : LeftOre A) (hS : S1 A)
    (n r : ℕ) (hr : 0 < r) : FreeAnchoredWidthBound (A := A) n r := by
  have : Module.Free Aᵐᵒᵖ A := Module.Free.of_equiv (unopLinear A)
  intro d a hd ha B
  exact projective_anchored_width hL hS d a ha (oreRank_free n) hd hr B

/-- The rank-two case on `A^3` has two terms, including arbitrary offsets
and every injective affine tail. -/
theorem rank_two_three (hL : LeftOre A) (hS : S1 A)
    (d a : Module.End Aᵐᵒᵖ (Fin 3 → A))
    (hd : localizedImageRank d = 2) (ha : Function.Injective a)
    (B : Module.End Aᵐᵒᵖ (Fin 3 → A)) :
    ∃ H U₀ U₁ : Module.End Aᵐᵒᵖ (Fin 3 → A),
      1 = d * U₀ + (B + H * a) * d * U₁ := by
  obtain ⟨H, U₀, U, h⟩ := free_anchored_width hL hS 3 2 (by omega) d a hd ha
    (fun _ => B)
  exact ⟨H 0, U₀, U 0, by simpa using h⟩

end GeneralizedStafford.ProjectiveWidth
