module

public import GeneralizedStafford.ProjectiveWidth.Generation
public import Mathlib.Algebra.Module.Projective

@[expose] public section

/-!
# Integral reconstruction from cleared denominators

This is the integral reconstruction step in §2 of
`docs/projective-anchored-width.md` in the research repository. The
denominator certificate and quotient-rank estimate are explicit inputs.
They are intermediate algebraic conditions. `Theorem.lean` constructs
them from the rank of `d` using `Denominators.lean` and `Rank.lean`.
-/

namespace GeneralizedStafford.ProjectiveWidth

open MulOpposite Submodule
open scoped nonZeroDivisors

section Assembly

variable {R P : Type*} [Ring R] [AddCommGroup P] [Module R P]
    [Module.Projective R P]

/-- A finite family whose images generate a projective module has an integral
right inverse, expressed as an identity in its endomorphism ring. -/
theorem endomorphism_sum_of_range (ι : Type*) [Fintype ι]
    (f : ι → Module.End R P) (hf : (⨆ i, LinearMap.range (f i)) = ⊤) :
    ∃ u : ι → Module.End R P, ∑ i, f i * u i = 1 := by
  classical
  let F : (ι → P) →ₗ[R] P := ∑ i, (f i).comp (LinearMap.proj i)
  have hF : LinearMap.range F = ⊤ := by
    apply eq_top_iff.mpr
    rw [← hf]
    apply iSup_le
    intro i p hp
    obtain ⟨x, rfl⟩ := hp
    refine ⟨Pi.single i x, ?_⟩
    simp [F, Pi.single_apply, apply_ite]
  obtain ⟨s, hs⟩ := F.exists_rightInverse_of_surjective hF
  refine ⟨fun i => (LinearMap.proj i).comp s, ?_⟩
  ext p
  have h := LinearMap.congr_fun hs p
  simpa [F, Module.End.mul_apply] using h

end Assembly

variable {A : Type*} [Ring A] [IsDomain A]
    [OreLocalization.OreSet (Aᵐᵒᵖ)⁰]
variable {P : Type*} [AddCommGroup P] [Module Aᵐᵒᵖ P]

/-- An anchored affine identity with `ell` additional terms, in the original
endomorphism ring. Products of endomorphisms mean composition. -/
def AffineAnchoredIdentity {ι : Type*} [Fintype ι]
    (d a : Module.End Aᵐᵒᵖ P) (B : ι → Module.End Aᵐᵒᵖ P) : Prop :=
  ∃ (H : ι → Module.End Aᵐᵒᵖ P) (U₀ : Module.End Aᵐᵒᵖ P)
    (U : ι → Module.End Aᵐᵒᵖ P),
    1 = d * U₀ + ∑ i, (B i + H i * a) * d * U i

/-- **Integral reconstruction.** A cleared left denominator on selected
columns, together with enough slots for the quotient rank, suffices for the
affine anchored identity. `Pi.single j c` uses left coordinate multiplication:
there is no noncentral right-scalar endomorphism of `P` hidden in the input.

The construction of these inputs is supplied by `projective_anchored_width`.
This separate lemma isolates the integral projective lifting step. -/
theorem reconstruct_of_denominator [Module.Finite Aᵐᵒᵖ P]
    [Module.Projective Aᵐᵒᵖ P] (hS : S1 A)
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (d a : Module.End Aᵐᵒᵖ P) (B : ι → Module.End Aᵐᵒᵖ P)
    (E : (κ → A) →ₗ[Aᵐᵒᵖ] P) (Z : P →ₗ[Aᵐᵒᵖ] (κ → A))
    {c : A} (hc : c ≠ 0)
    (hZ : ∀ j, Z (a (d (E (Pi.single j 1)))) = Pi.single j c)
    (hslots : oreRank A (P ⧸ LinearMap.range d) + 1 ≤
      Fintype.card ι * Fintype.card κ) :
    AffineAnchoredIdentity d a B := by
  classical
  let W := LinearMap.range d
  let T : κ → P := fun j => d (E (Pi.single j 1))
  let b : ι × κ → P ⧸ W := fun ij => W.mkQ (B ij.1 (T ij.2))
  obtain ⟨y, hy⟩ := prescribed_generators hS
    (by simpa only [Fintype.card_prod] using hslots) b hc
  choose yP hyP using fun ij => W.mkQ_surjective (y ij)
  let Y : ι → (κ → A) →ₗ[Aᵐᵒᵖ] P := fun i => combo (fun j => yP (i, j))
  let H : ι → Module.End Aᵐᵒᵖ P := fun i => (Y i).comp Z
  let g : ι × κ → P := fun ij => (B ij.1 + H ij.1 * a) (T ij.2)
  have hY : ∀ i j, Y i (Pi.single j c) = op c • yP (i, j) := by
    intro i j
    simp [Y, combo_apply, Pi.single_apply, apply_ite]
  have hg : ∀ ij, W.mkQ (g ij) = b ij + op c • y ij := by
    rintro ⟨i, j⟩
    change W.mkQ (B i (T j) + Y i (Z (a (T j)))) = b (i, j) + op c • y (i, j)
    rw [show Z (a (T j)) = Pi.single j c from hZ j, hY, map_add, map_smul, hyP]
  have hspan : span Aᵐᵒᵖ (Set.range (W.mkQ ∘ g)) = ⊤ := by
    have he : W.mkQ ∘ g = fun ij => b ij + op c • y ij := by
      funext ij
      exact hg ij
    rw [he]
    exact hy
  have htop : W ⊔ span Aᵐᵒᵖ (Set.range g) = ⊤ := by
    rw [← comap_map_mkQ, map_span, ← Set.range_comp, hspan, comap_top]
  let f : Option ι → Module.End Aᵐᵒᵖ P :=
    fun o => o.elim d (fun i => (B i + H i * a) * d)
  have hf : (⨆ o, LinearMap.range (f o)) = ⊤ := by
    apply eq_top_iff.mpr
    rw [← htop]
    apply sup_le
    · exact le_iSup (fun o => LinearMap.range (f o)) none
    · rw [span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      apply (le_iSup (fun o => LinearMap.range (f o)) (some i))
      exact ⟨E (Pi.single j 1), rfl⟩
  obtain ⟨u, hu⟩ := endomorphism_sum_of_range (Option ι) f hf
  refine ⟨H, u none, fun i => u (some i), ?_⟩
  simpa only [Fintype.sum_option, f, Option.elim_none, Option.elim_some, mul_assoc]
    using hu.symm

/-- Rank of the localized image of an endomorphism, using Mathlib's
Ore localization of the right module. `QΛ A` is the division ring of
fractions of `Aᵐᵒᵖ`, so this is right dimension over the fractions of `A`. -/
noncomputable def localizedImageRank (d : Module.End Aᵐᵒᵖ P) : ℕ :=
  Module.finrank (QΛ A) (LinearMap.range (locMap (Λ := A) d))

/-- Exact free-module form of the conditional width assertion, with `n / r`
additional slots (hence `n/r+1` terms). Proved from bilateral Ore and scalar
S1 by `free_anchored_width`; the definition itself introduces no axiom. -/
def FreeAnchoredWidthBound (n r : ℕ) : Prop :=
  ∀ d a : Module.End Aᵐᵒᵖ (Fin n → A),
    localizedImageRank d = r → Function.Injective a →
    ∀ B : Fin (n / r) → Module.End Aᵐᵒᵖ (Fin n → A),
      AffineAnchoredIdentity d a B

end GeneralizedStafford.ProjectiveWidth
