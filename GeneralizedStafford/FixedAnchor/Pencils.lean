module

public import GeneralizedStafford.FixedAnchor.GermTests
public import AlgebraicAnalysis.LinearAlgebra.ActivatedPencil

@[expose] public section

/-!
# Activated pencils on finite critical germ tests

These statements concern actual module germs. Joint injectivity is the dual
form of generation by `v` and `uL`; it is an input to this pencil lemma, not
an assumption that the desired pencil is epic.
-/

namespace GeneralizedStafford.FixedAnchor

open Module Module.Germ MulOpposite AlgebraicAnalysis

universe u v w
variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]
  [IsNoetherian Rᵐᵒᵖ M]
variable {C : Type w} [AddCommGroup C] [Module Rᵐᵒᵖ C] [IsNoetherian Rᵐᵒᵖ C]
variable {k : Type*} [Field k] [Algebra k R] {e : ℕ}

/-- Activated pencils on a finite critical Schur space. The action `vL=0`
and the joint map retain the right multiplication order. -/
theorem activated_germ_test_finite
    (hM : Module.DevLE Rᵐᵒᵖ e M) (hC : Module.Critical Rᵐᵒᵖ e C)
    (v u : Section R e M) (L : R) (hvL : op L • v = 0)
    (hjoint : Function.Injective (fun h : Hom Rᵐᵒᵖ e M C =>
      (Hom.comp h v, op L • Hom.comp h u))) :
    {c : k | ¬ Function.Injective (fun h : Hom Rᵐᵒᵖ e M C =>
      Hom.comp h (v + op (algebraMap k R c) • u))}.Finite := by
  classical
  letI := End.divisionRing hC
  letI := Hom.finite_of_devLE hM hC
  let κ : k →+* End Rᵐᵒᵖ e C := End.centralMap.comp (oppositeCentralField (R := R) k)
  let P := Hom.precompLinear (C := C) v
  let Q := Hom.precompLinear (C := C) u
  let T := TorsionEscape.rightMulLinear (E := End Rᵐᵒᵖ e C) L (W := Section R e C)
  have hTP : T.comp P = 0 := by
    ext h
    change Hom.comp (Hom.comp h v) (Hom.ofLinearMap (Section.leftMul L)) = 0
    rw [Hom.comp_assoc]
    change Hom.comp h (op L • v) = 0
    rw [hvL]
    exact PartialHom.comp_zero h
  have hf := activated_pencil_finite κ
    (fun c x => (End.centralMap_commute (oppositeCentralField (R := R) k c) x).eq)
    P Q T hTP hjoint
  convert hf using 1
  ext c
  have heq : (fun h : Hom Rᵐᵒᵖ e M C =>
      Hom.comp h (v + op (algebraMap k R c) • u)) =
      (fun h => P h + κ c • Q h) := by
    funext h
    rw [Hom.comp_add]
    change Hom.comp h v + Hom.comp h (Hom.comp u (Hom.ofLinearMap
        (Section.leftMul (algebraMap k R c)))) = Hom.comp h v + κ c • Hom.comp h u
    rw [← Hom.comp_assoc]
    exact congrArg (Hom.comp h v + ·)
      (section_central_scalar (oppositeCentralField (R := R) k c) (Hom.comp h u))
  simp only [Set.mem_ofPred_eq, heq]

/-- Finite critical separation turns the activated dual pencils into an
actual epic germ outside finitely many central scalars. -/
theorem activated_germ_pencil_finite
    (hM : Module.DevLE Rᵐᵒᵖ e M) (F : Module.CriticalFiltration Rᵐᵒᵖ e M)
    (v u : Section R e M) (L : R) (hvL : op L • v = 0)
    (hjoint : ∀ i : F.TopIndex, Function.Injective
      (fun h : Hom Rᵐᵒᵖ e M (F.TopFactor i) =>
        (Hom.comp h v, op L • Hom.comp h u))) :
    {c : k | ¬ Hom.Epic (v + op (algebraMap k R c) • u)}.Finite := by
  classical
  have hfin : (⋃ i : F.TopIndex,
      {c : k | ¬ Function.Injective (fun h : Hom Rᵐᵒᵖ e M (F.TopFactor i) =>
        Hom.comp h (v + op (algebraMap k R c) • u))}).Finite :=
    Set.finite_iUnion fun i => activated_germ_test_finite hM (F.topFactor_critical i)
      v u L hvL (hjoint i)
  refine hfin.subset ?_
  intro c hc
  by_contra hn
  apply hc
  apply (Hom.epic_iff_injective_comp_topFactors hM F _).mpr
  intro i
  by_contra hi
  exact hn (Set.mem_iUnion.mpr ⟨i, hi⟩)

/-- An already epic germ stays epic along any central pencil outside a
finite set. This supplies preservation of each old finite germ test. -/
theorem germ_pencil_finite
    (hM : Module.DevLE Rᵐᵒᵖ e M) (F : Module.CriticalFiltration Rᵐᵒᵖ e M)
    (v u : Section R e M) (hv : Hom.Epic v) :
    {c : k | ¬ Hom.Epic (v + op (algebraMap k R c) • u)}.Finite := by
  apply activated_germ_pencil_finite hM F v u 0 (zero_smul _ _)
  intro i h h' he
  exact hv.right_cancel h h' (congrArg Prod.fst he)

end GeneralizedStafford.FixedAnchor
