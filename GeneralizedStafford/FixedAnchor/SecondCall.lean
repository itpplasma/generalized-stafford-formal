module

public import GeneralizedStafford.FixedAnchor.Reduction
public import GeneralizedStafford.FixedAnchor.Pencils

@[expose] public section

/-!
# The second-call test and the activated pencil

The epic canonical test modulo `I` makes the pair `(fd, gdL)` epic
modulo `J`. Cancellation by that pair gives the required joint injectivity
on actual germ Hom spaces, without a splitting of either quotient.
-/

namespace GeneralizedStafford.FixedAnchor

open Module Module.Germ MulOpposite AlgebraicAnalysis
open AlgebraicAnalysis.ColonSupport AlgebraicAnalysis.DenominatorTorsion

universe u v
variable {R : Type u} [Ring R] [IsNoetherian Rᵐᵒᵖ R] {e : ℕ}

/-- The two actual numerator maps used by the activated pencil. -/
def secondCallPair (d f g L : R) :
    (R × R) →ₗ[Rᵐᵒᵖ] (R ⧸ refinedIdeal d f g) :=
  (((refinedIdeal d f g).mkQ.comp (leftMulLinear (f * d))).comp
      (LinearMap.fst Rᵐᵒᵖ R R)) +
    (((refinedIdeal d f g).mkQ.comp (leftMulLinear (g * d * L))).comp
      (LinearMap.snd Rᵐᵒᵖ R R))

/-- The canonical second-call test implies epicity of the combined map
`(x,y) ↦ fd*x + gdL*y` modulo the colon refinement. -/
theorem secondCallPair_epic (d f g L : R)
    (htest : Hom.Epic (Hom.ofLinearMap (e := e)
      ((firstIdeal d f).mkQ.comp (leftMulLinear (g * d * L))))) :
    Hom.Epic (Hom.ofLinearMap (e := e) (secondCallPair d f g L)) := by
  let J := refinedIdeal d f g
  let p := secondCallPair d f g L
  let Z := (R ⧸ J) ⧸ p.range
  let t : R →ₗ[Rᵐᵒᵖ] Z := p.range.mkQ.comp J.mkQ
  have ht (x y : R) : t (f * d * x + g * d * L * y) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨(x, y), by simp [p, secondCallPair]; rfl⟩
  have hI : firstIdeal d f ≤ t.ker := by
    apply sup_le
    · intro x hx
      change p.range.mkQ (J.mkQ x) = 0
      have hxJ : J.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_sup_left hx)
      rw [hxJ, map_zero]
    · rintro x ⟨s, rfl⟩
      change t (f * d * s) = 0
      simpa only [mul_zero, add_zero] using ht s 0
  let tI : (R ⧸ firstIdeal d f) →ₗ[Rᵐᵒᵖ] Z := (firstIdeal d f).liftQ t hI
  have htI : Function.Surjective tI := by
    intro z
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective p.range z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective J w
    exact ⟨(firstIdeal d f).mkQ x, rfl⟩
  have hz : Hom.comp (Hom.ofLinearMap (e := e) tI)
      (Hom.ofLinearMap ((firstIdeal d f).mkQ.comp (leftMulLinear (g * d * L)))) = 0 := by
    rw [← Hom.ofLinearMap_comp]
    apply (Hom.ofLinearMap_eq_zero_iff _).mpr
    have he : tI.comp ((firstIdeal d f).mkQ.comp (leftMulLinear (g * d * L))) = 0 := by
      apply LinearMap.ext
      intro x
      change t (g * d * L * x) = 0
      simpa only [mul_zero, zero_add] using ht 0 x
    rw [he, LinearMap.range_zero]
    exact Module.small_of_subsingleton e
  have hzI : Hom.ofLinearMap (e := e) tI = 0 :=
    htest.right_cancel _ 0 (by simpa only [PartialHom.zero_comp] using hz)
  have hs := (Hom.ofLinearMap_eq_zero_iff tI).mp hzI
  exact (Hom.epic_ofLinearMap_iff p).mpr
    (hs.of_surjective tI.range.subtype (by
      intro z
      obtain ⟨x, rfl⟩ := htI z
      exact ⟨⟨tI x, ⟨x, rfl⟩⟩, rfl⟩))

/-- The relation `fdL=dC` makes `vL` zero already as a total map. -/
theorem secondCall_vL_zero (d f g L C : R) (hrel : f * d * L = d * C) :
    op L • (Hom.ofLinearMap (e := e)
      ((refinedIdeal d f g).mkQ.comp (leftMulLinear (f * d)))) = 0 := by
  change Hom.comp (Hom.ofLinearMap _) (Hom.ofLinearMap (Section.leftMul L)) = 0
  rw [← Hom.ofLinearMap_comp]
  apply (Hom.ofLinearMap_eq_zero_iff _).mpr
  have he : ((refinedIdeal d f g).mkQ.comp (leftMulLinear (f * d))).comp
      (Section.leftMul L) = 0 := by
    apply LinearMap.ext
    intro x
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply Submodule.mem_sup_left
    exact ⟨C * x, by change d * (C * x) = f * d * (L * x); rw [← mul_assoc, ← hrel, mul_assoc]⟩
  rw [he, LinearMap.range_zero]
  exact Module.small_of_subsingleton e

/-- The second-call test supplies the activated pencil's joint injectivity
for every Noetherian target, hence for each retained critical Schur type. -/
theorem secondCall_joint_injective
    {S : Type v} [AddCommGroup S] [Module Rᵐᵒᵖ S]
    (d f g L : R)
    (htest : Hom.Epic (Hom.ofLinearMap (e := e)
      ((firstIdeal d f).mkQ.comp (leftMulLinear (g * d * L))))) :
    Function.Injective (fun h : Hom Rᵐᵒᵖ e (R ⧸ refinedIdeal d f g) S =>
      (Hom.comp h (Hom.ofLinearMap
        ((refinedIdeal d f g).mkQ.comp (leftMulLinear (f * d)))),
       op L • Hom.comp h (Hom.ofLinearMap
        ((refinedIdeal d f g).mkQ.comp (leftMulLinear (g * d)))))) := by
  intro h h' he
  have hv := congrArg Prod.fst he
  dsimp only at hv
  have hw := congrArg Prod.snd he
  have hmul : (leftMulLinear (g * d)).comp (Section.leftMul L) =
      leftMulLinear (g * d * L) := by
    apply LinearMap.ext
    intro x
    exact (mul_assoc _ _ _).symm
  have hw' : Hom.comp h (Hom.ofLinearMap
      ((refinedIdeal d f g).mkQ.comp (leftMulLinear (g * d * L)))) =
      Hom.comp h' (Hom.ofLinearMap
      ((refinedIdeal d f g).mkQ.comp (leftMulLinear (g * d * L)))) := by
    change Hom.comp (Hom.comp h _) (Hom.ofLinearMap (Section.leftMul L)) =
      Hom.comp (Hom.comp h' _) (Hom.ofLinearMap (Section.leftMul L)) at hw
    simpa only [Hom.comp_assoc, ← Hom.ofLinearMap_comp, LinearMap.comp_assoc, hmul] using hw
  apply (secondCallPair_epic d f g L htest).right_cancel
  change Hom.comp h (Hom.ofLinearMap (_ + _)) =
    Hom.comp h' (Hom.ofLinearMap (_ + _))
  rw [Hom.ofLinearMap_add, Hom.comp_add, Hom.comp_add]
  congr 1
  · rw [Hom.ofLinearMap_comp, ← Hom.comp_assoc, hv, Hom.comp_assoc,
      ← Hom.ofLinearMap_comp]
  · rw [Hom.ofLinearMap_comp, ← Hom.comp_assoc, hw', Hom.comp_assoc,
      ← Hom.ofLinearMap_comp]

/-- The concrete second-call test discharges every hypothesis of the
activated finite-exception theorem. -/
theorem secondCall_pencil_finite {k : Type*} [Field k] [Algebra k R]
    (d f g L C : R) (hrel : f * d * L = d * C)
    (hW : Module.DevLE Rᵐᵒᵖ e (R ⧸ refinedIdeal d f g))
    (htest : Hom.Epic (Hom.ofLinearMap (e := e)
      ((firstIdeal d f).mkQ.comp (leftMulLinear (g * d * L))))) :
    {c : k | ¬ Hom.Epic
      (Hom.ofLinearMap (e := e) ((refinedIdeal d f g).mkQ.comp (leftMulLinear (f * d))) +
        op (algebraMap k R c) • Hom.ofLinearMap
          ((refinedIdeal d f g).mkQ.comp (leftMulLinear (g * d))))}.Finite := by
  classical
  let F := Classical.choice hW.nonempty_criticalFiltration
  exact activated_germ_pencil_finite hW F _ _ L
    (secondCall_vL_zero d f g L C hrel)
    (fun _ => secondCall_joint_injective d f g L htest)

/-- A total quotient section is epic precisely when its enlarged ideal has
small quotient. This is the concrete cokernel used in descent. -/
theorem quotient_section_epic_iff (J : Submodule Rᵐᵒᵖ R) (x : R) :
    Hom.Epic (Hom.ofLinearMap (e := e) (J.mkQ.comp (leftMulLinear x))) ↔
      Module.Small Rᵐᵒᵖ e (R ⧸ (J ⊔ principalRightIdeal x)) := by
  rw [Hom.epic_ofLinearMap_iff]
  have hr : (J.mkQ.comp (leftMulLinear x)).range =
      (principalRightIdeal x).map J.mkQ := by
    rw [LinearMap.range_comp]
    rfl
  rw [hr]
  exact Module.small_linearEquiv_iff e
    (Submodule.quotientQuotientEquivQuotientSup J (principalRightIdeal x))

end GeneralizedStafford.FixedAnchor
