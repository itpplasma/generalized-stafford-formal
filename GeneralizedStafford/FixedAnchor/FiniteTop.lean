module

public import GeneralizedStafford.FixedAnchor.Reduction
public import GeneralizedStafford.FixedAnchor.GermTests

@[expose] public section

/-!
# One finite top stratum with a fixed principal anchor

Finite affine germ tests can be satisfied together with generation at the top
stratum of `R/dR`. At deviation zero this already gives the integral affine
Stafford identity. Iteration at positive deviation still needs the mixed-anchor
activated-pencil descent; it is not a consequence of repeatedly applying this
one-stratum statement to `R/dR`.
-/

namespace GeneralizedStafford.FixedAnchor

open Module Module.Germ MulOpposite AlgebraicAnalysis
open AlgebraicAnalysis.ColonSupport AlgebraicAnalysis.DenominatorTorsion

universe u
variable {R : Type u} [Ring R] [IsDomain R] [IsSimpleRing R]
  [IsNoetherian Rᵐᵒᵖ R]
variable {k : Type*} [Field k] [Infinite k] [Algebra k R]
include k

/-- Top-stratum generation and any finite list of actual epic germ tests,
with the same prescribed affine source and the original principal anchor. -/
theorem exists_affine_small_with_tests {n : ℕ} {d a : R}
    (hd : d ≠ 0) (ha : a ≠ 0)
    (hdev : Module.DevLE Rᵐᵒᵖ n (R ⧸ anchor d))
    {ι : Type*} [Fintype ι] (e : ι → ℕ) (M : ι → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module Rᵐᵒᵖ (M i)]
    [∀ i, IsNoetherian Rᵐᵒᵖ (M i)]
    (hM : ∀ i, Module.DevLE Rᵐᵒᵖ (e i) (M i))
    (ht : ∀ i, IsTorsionRight (R := R) (M := M i))
    (q z : ∀ i, Hom Rᵐᵒᵖ (e i) R (M i)) (hq : ∀ i, Hom.Epic (q i))
    (b : ι → R) (hb : ∀ i, b i ≠ 0) (B : R) :
    ∃ H : R, Module.Small Rᵐᵒᵖ n (R ⧸ firstIdeal d (B + H * a)) ∧
      ∀ i, Hom.Epic (z i + op ((B + H * a) * b i) • q i) := by
  classical
  let e' : Option ι → ℕ | none => n | some i => e i
  let M' : Option ι → Type u | none => R ⧸ anchor d | some i => M i
  letI : ∀ i, AddCommGroup (M' i) := fun i => by cases i <;> dsimp [M'] <;> infer_instance
  letI : ∀ i, Module Rᵐᵒᵖ (M' i) := fun i => by cases i <;> dsimp [M'] <;> infer_instance
  letI : ∀ i, IsNoetherian Rᵐᵒᵖ (M' i) := fun i => by cases i <;> dsimp [M'] <;> infer_instance
  let q' : ∀ i, Hom Rᵐᵒᵖ (e' i) R (M' i)
    | none => Hom.ofLinearMap (anchor d).mkQ
    | some i => q i
  let z' : ∀ i, Hom Rᵐᵒᵖ (e' i) R (M' i) | none => 0 | some i => z i
  let b' : Option ι → R | none => d | some i => b i
  have hM' : ∀ i, Module.DevLE Rᵐᵒᵖ (e' i) (M' i) := by
    intro i; cases i with
    | none => exact hdev
    | some i => exact hM i
  have ht' : ∀ i, IsTorsionRight (R := R) (M := M' i) := by
    intro i; cases i with
    | none =>
      exact quotient_isTorsion_of_principal_le
        (OreRightIntersection.rightOreCondition_of_isNoetherian (R := R)) d hd (anchor d) le_rfl
    | some i => exact ht i
  have hq' : ∀ i, Hom.Epic (q' i) := by
    intro i; cases i with
    | none => exact Hom.epic_ofLinearMap_of_surjective _ (Submodule.mkQ_surjective _)
    | some i => exact hq i
  have hb' : ∀ i, b' i ≠ 0 := by
    intro i; cases i with
    | none => exact hd
    | some i => exact hb i
  obtain ⟨H, hH⟩ := exists_affine_epic_tests (k := k) e' M' hM' ht' q' z' hq' b' hb' ha B
  refine ⟨H, ?_, fun i => hH (some i)⟩
  have hep : Hom.Epic (Hom.ofLinearMap (e := n)
      ((anchor d).mkQ.comp (Section.leftMul ((B + H * a) * d)))) := by
    have h := hH none
    change Hom.Epic (0 + Hom.comp (Hom.ofLinearMap (anchor d).mkQ)
      (Hom.ofLinearMap (Section.leftMul ((B + H * a) * d)))) at h
    simpa only [zero_add, ← Hom.ofLinearMap_comp] using h
  have hs := (Hom.epic_ofLinearMap_iff _).mp hep
  have hr : ((anchor d).mkQ.comp (Section.leftMul ((B + H * a) * d))).range =
      (principalRightIdeal ((B + H * a) * d)).map (anchor d).mkQ := by
    rw [LinearMap.range_comp]
    rfl
  rw [hr] at hs
  exact (Module.small_linearEquiv_iff n
    (Submodule.quotientQuotientEquivQuotientSup (anchor d)
      (principalRightIdeal ((B + H * a) * d)))).mp hs

/-- Complete fixed-anchor affine S1 when the principal quotient has deviation
zero (equivalently is Artinian), carrying finite epic germ tests. -/
theorem affine_of_devLE_zero_with_tests {d a : R} (hd : d ≠ 0) (ha : a ≠ 0)
    (hdev : Module.DevLE Rᵐᵒᵖ 0 (R ⧸ anchor d))
    {ι : Type*} [Fintype ι] (e : ι → ℕ) (M : ι → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module Rᵐᵒᵖ (M i)]
    [∀ i, IsNoetherian Rᵐᵒᵖ (M i)]
    (hM : ∀ i, Module.DevLE Rᵐᵒᵖ (e i) (M i))
    (ht : ∀ i, IsTorsionRight (R := R) (M := M i))
    (q z : ∀ i, Hom Rᵐᵒᵖ (e i) R (M i)) (hq : ∀ i, Hom.Epic (q i))
    (b : ι → R) (hb : ∀ i, b i ≠ 0) (B : R) :
    ∃ H U V : R, 1 = d * U + (B + H * a) * d * V ∧
      ∀ i, Hom.Epic (z i + op ((B + H * a) * b i) • q i) := by
  obtain ⟨H, hsmall, htests⟩ :=
    exists_affine_small_with_tests (k := k) hd ha hdev e M hM ht q z hq b hb B
  obtain ⟨U, V, hUV⟩ := coefficients_of_small_zero d (B + H * a) hsmall
  exact ⟨H, U, V, hUV, htests⟩

/-- The integral fixed-anchor identity for an Artinian principal quotient,
without any filtration or finite-dimensionality assumption on the ring. -/
theorem affine_of_devLE_zero {d a : R} (hd : d ≠ 0) (ha : a ≠ 0)
    (hdev : Module.DevLE Rᵐᵒᵖ 0 (R ⧸ anchor d)) (B : R) :
    ∃ H U V : R, 1 = d * U + (B + H * a) * d * V := by
  obtain ⟨H, U, V, hUV, _⟩ := affine_of_devLE_zero_with_tests (k := k) hd ha hdev
    (fun _ : Fin 0 => 0) (fun _ => R) (fun i => i.elim0) (fun i => i.elim0)
    (fun _ => 0) (fun _ => 0) (fun i => i.elim0) (fun _ => 1) (fun i => i.elim0) B
  exact ⟨H, U, V, hUV⟩

end GeneralizedStafford.FixedAnchor
