module

public import AlgebraicAnalysis.Module.DualSeparationGeneral
public import AlgebraicAnalysis.Module.TorsionEscape
public import Mathlib.Algebra.Algebra.Opposite

@[expose] public section

/-!
# Finite affine critical germ tests

All tests here are actual module germs. No correspondence with arbitrary
Gabriel-quotient objects is asserted. A test uses a finite-deviation target,
an epic source germ, a critical torsion dual type, an offset and a nonzero
right tail. Finiteness of each Schur space is proved upstream from deviation.
-/

namespace GeneralizedStafford.FixedAnchor

open Module Module.Germ MulOpposite
open AlgebraicAnalysis

universe u v
variable {R : Type u} [Ring R] {C : Type v} [AddCommGroup C] [Module Rᵐᵒᵖ C] {e : ℕ}

/-- Central right scalars on sections agree with their left Schur action,
including for germs represented only on dense submodules. -/
theorem section_central_scalar (a : Subring.center Rᵐᵒᵖ) (w : Section R e C) :
    a.val • w = End.centralMap (R := Rᵐᵒᵖ) (e := e) (C := C) a • w := by
  have he : Hom.reducedMap (e := e) (End.centralScalar (C := C) a) =
      End.centralScalar (C := C ⧸ smallRadical Rᵐᵒᵖ e C) a := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (smallRadical Rᵐᵒᵖ e C) x
    rfl
  have hs : Hom.reducedMap (e := e) (Section.leftMul (unop a.val)) =
      End.centralScalar (C := R ⧸ smallRadical Rᵐᵒᵖ e R) a := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (smallRadical Rᵐᵒᵖ e R) x
    change (smallRadical Rᵐᵒᵖ e R).mkQ (unop a.val * x) =
      (smallRadical Rᵐᵒᵖ e R).mkQ (x * unop a.val)
    congr 1
    exact congrArg unop (Subring.mem_center_iff.mp a.property (op x))
  change PartialHom.comp w (PartialHom.ofLinearMap _) =
    PartialHom.comp (PartialHom.ofLinearMap _) w
  rw [he, hs]
  induction w using Quotient.inductionOn with | _ w =>
  apply Quotient.sound
  apply Representative.rel_of_eq
  intro x hx hy
  have hm := w.val.toFun.map_smul a.val (⟨x, w.pullback_le _ hy⟩ : w.val.domain)
  exact hm

section Field

variable (k : Type*) [Field k] [Algebra k R]

/-- A central field in the opposite scalar ring; `Algebra k R` states
centrality and its field map is injective when `R` is nontrivial. -/
def oppositeCentralField : k →+* Subring.center Rᵐᵒᵖ :=
  (algebraMap k Rᵐᵒᵖ).codRestrict _ (fun c =>
    Subring.mem_center_iff.mpr fun r => (Algebra.commutes c r).symm)

end Field

/-- Simultaneous finite critical germ tests with prescribed affine tail.
This is source selection, with no dimension-lowering conclusion assumed. -/
theorem exists_affine_germ_tests
    [IsDomain R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    {k : Type*} [Field k] [Infinite k] [Algebra k R]
    {ι : Type*} [Fintype ι] (e : ι → ℕ) (M C : ι → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module Rᵐᵒᵖ (M i)]
    [∀ i, IsNoetherian Rᵐᵒᵖ (M i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module Rᵐᵒᵖ (C i)]
    [∀ i, IsNoetherian Rᵐᵒᵖ (C i)]
    (hM : ∀ i, Module.DevLE Rᵐᵒᵖ (e i) (M i))
    (hC : ∀ i, Module.Critical Rᵐᵒᵖ (e i) (C i))
    (ht : ∀ i, DenominatorTorsion.IsTorsionRight (R := R) (M := C i))
    (q z : ∀ i, Hom Rᵐᵒᵖ (e i) R (M i)) (hq : ∀ i, Hom.Epic (q i))
    (b : ι → R) (hb : ∀ i, b i ≠ 0) {a : R} (ha : a ≠ 0) (B : R) :
    ∃ H : R, ∀ i, Function.Injective
      (fun h : Hom Rᵐᵒᵖ (e i) (M i) (C i) =>
        Hom.comp h (z i + op ((B + H * a) * b i) • q i)) := by
  classical
  letI : ∀ i, DivisionRing (End Rᵐᵒᵖ (e i) (C i)) := fun i => End.divisionRing (hC i)
  letI : ∀ i, Module.Finite (End Rᵐᵒᵖ (e i) (C i))
      (Hom Rᵐᵒᵖ (e i) (M i) (C i)) := fun i => Hom.finite_of_devLE (hM i) (hC i)
  let κ (i : ι) : k →+* End Rᵐᵒᵖ (e i) (C i) :=
    End.centralMap.comp (oppositeCentralField (R := R) k)
  let P (i : ι) := Hom.precompLinear (C := C i) (q i)
  let Z (i : ι) := Hom.precompLinear (C := C i) (z i)
  obtain ⟨H, hH⟩ := TorsionEscape.exists_affine_source
    (OreRightIntersection.rightOreCondition_of_isNoetherian (R := R))
    (fun i => Section.torsion (hC i) (ht i))
    (algebraMap k R) κ
    (fun i c x => (End.centralMap_commute (oppositeCentralField (R := R) k c) x).eq)
    (fun i c w => section_central_scalar (oppositeCentralField (R := R) k c) w)
    P Z (fun i => (hq i).right_cancel)
    Finset.univ b (fun i _ => hb i) ha B
  refine ⟨H, fun i => ?_⟩
  have hi := hH i (Finset.mem_univ i)
  convert hi using 1
  funext h
  exact Hom.comp_add h (z i) (op ((B + H * a) * b i) • q i) |>.trans
    (congrArg (Hom.comp h (z i) + ·)
      (Hom.comp_assoc h (q i) (Hom.ofLinearMap (Section.leftMul _))).symm)

/-- Finite affine selection for epic germ tests. Each finite-deviation torsion
target contributes its finite list of retained critical factors. -/
theorem exists_affine_epic_tests
    [IsDomain R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    {k : Type*} [Field k] [Infinite k] [Algebra k R]
    {ι : Type*} [Fintype ι] (e : ι → ℕ) (M : ι → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module Rᵐᵒᵖ (M i)]
    [∀ i, IsNoetherian Rᵐᵒᵖ (M i)]
    (hM : ∀ i, Module.DevLE Rᵐᵒᵖ (e i) (M i))
    (ht : ∀ i, DenominatorTorsion.IsTorsionRight (R := R) (M := M i))
    (q z : ∀ i, Hom Rᵐᵒᵖ (e i) R (M i)) (hq : ∀ i, Hom.Epic (q i))
    (b : ι → R) (hb : ∀ i, b i ≠ 0) {a : R} (ha : a ≠ 0) (B : R) :
    ∃ H : R, ∀ i, Hom.Epic (z i + op ((B + H * a) * b i) • q i) := by
  classical
  let F (i : ι) : Module.CriticalFiltration Rᵐᵒᵖ (e i) (M i) :=
    Classical.choice (hM i).nonempty_criticalFiltration
  let J := (i : ι) × (F i).TopIndex
  let C (j : J) := (F j.1).TopFactor j.2
  have hC (j : J) : Module.Critical Rᵐᵒᵖ (e j.1) (C j) :=
    (F j.1).topFactor_critical j.2
  have htC (j : J) : DenominatorTorsion.IsTorsionRight (R := R) (M := C j) := by
    let U := (F j.1).toRelSeries j.2.val.succ
    let V := ((F j.1).toRelSeries j.2.val.castSucc).comap U.subtype
    exact DenominatorTorsion.isTorsionRight_of_surjective V.mkQ V.mkQ_surjective
      (DenominatorTorsion.isTorsionRight_of_injective U.subtype Subtype.val_injective (ht j.1))
  obtain ⟨H, hH⟩ := exists_affine_germ_tests (k := k)
    (fun j : J => e j.1) (fun j => M j.1) C
    (fun j => hM j.1) hC htC (fun j => q j.1) (fun j => z j.1)
    (fun j => hq j.1) (fun j => b j.1) (fun j => hb j.1) ha B
  exact ⟨H, fun i => (Hom.epic_iff_injective_comp_topFactors (hM i) (F i) _).mpr
    (fun j => hH ⟨i, j⟩)⟩

end GeneralizedStafford.FixedAnchor
