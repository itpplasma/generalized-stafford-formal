module

public import GeneralizedStafford.FixedAnchor.SecondCall
public import GeneralizedStafford.FixedAnchor.FiniteTop

@[expose] public section

/-!
# Fixed-anchor descent with finite tests

The test records below contain actual Noetherian torsion module germs.
The uniform bound is used twice with the same anchor and the exact
recursive tail; it is an induction invariant, not a source hypothesis
in the final theorem.
-/

namespace GeneralizedStafford.FixedAnchor

open Module Module.Germ MulOpposite AlgebraicAnalysis
open AlgebraicAnalysis.ColonSupport AlgebraicAnalysis.DenominatorTorsion

universe u
variable {R : Type u} [Ring R]

/-- A single actual epic germ test with its nonzero prescribed right tail. -/
structure EpicGermTest (R : Type u) [Ring R] where
  level : ℕ
  Target : Type u
  [addCommGroup : AddCommGroup Target]
  [module : Module Rᵐᵒᵖ Target]
  [noetherian : IsNoetherian Rᵐᵒᵖ Target]
  bounded : Module.DevLE Rᵐᵒᵖ level Target
  torsion : IsTorsionRight (R := R) (M := Target)
  q : Hom Rᵐᵒᵖ level R Target
  offset : Hom Rᵐᵒᵖ level R Target
  epic : Hom.Epic q
  tail : R
  tail_ne : tail ≠ 0

attribute [instance] EpicGermTest.addCommGroup EpicGermTest.module EpicGermTest.noetherian

/-- Satisfaction uses precomposition with left multiplication by `f*tail`. -/
def EpicGermTest.Satisfied (t : EpicGermTest R) (f : R) : Prop :=
  Hom.Epic (t.offset + op (f * t.tail) • t.q)

/-- The right action and central scalar have precisely the pencil order. -/
theorem test_pencil_identity {M : Type u} [AddCommGroup M] [Module Rᵐᵒᵖ M]
    {e : ℕ} (q z : Section R e M) (f g b lam : R)
    (hlam : ∀ x : R, lam * x = x * lam) :
    z + op ((f + lam * g) * b) • q =
      (z + op (f * b) • q) + op lam • (op (g * b) • q) := by
  have he : (f + lam * g) * b = f * b + (g * b) * lam := by
    rw [add_mul, mul_assoc, hlam]
  rw [he, op_add, add_smul, ← add_assoc, Section.right_action_assoc]

/-- Every old satisfied test has only finitely many bad central corrections. -/
theorem EpicGermTest.pencil_finite {k : Type*} [Field k] [Algebra k R]
    (t : EpicGermTest R) {f : R} (hf : t.Satisfied f) (g : R) :
    {c : k | ¬ t.Satisfied (f + algebraMap k R c * g)}.Finite := by
  classical
  let F := Classical.choice t.bounded.nonempty_criticalFiltration
  have hfin := germ_pencil_finite (k := k) t.bounded F
    (t.offset + op (f * t.tail) • t.q) (op (g * t.tail) • t.q) hf
  simpa only [EpicGermTest.Satisfied,
    test_pencil_identity _ _ _ _ _ _ (fun x => (Algebra.commutes _ x))] using hfin

/-- The activated pencil kills the current top stratum, outside finitely
many central scalars, in the actual two-generator quotient. -/
theorem secondCall_small_finite [IsNoetherian Rᵐᵒᵖ R]
    {k : Type*} [Field k] [Algebra k R] {e : ℕ}
    (d f g L C : R) (hrel : f * d * L = d * C)
    (hW : Module.DevLE Rᵐᵒᵖ e (R ⧸ refinedIdeal d f g))
    (htest : Hom.Epic (Hom.ofLinearMap (e := e)
      ((firstIdeal d f).mkQ.comp (leftMulLinear (g * d * L))))) :
    {c : k | ¬ Module.Small Rᵐᵒᵖ e
      (R ⧸ firstIdeal d (f + algebraMap k R c * g))}.Finite := by
  have hfin := secondCall_pencil_finite (k := k) d f g L C hrel hW htest
  refine hfin.subset ?_
  intro c hc hep
  apply hc
  let lam := algebraMap k R c
  have hlam (x : R) : lam * x = x * lam := (Algebra.commutes c x)
  have hp : Hom.Epic (Hom.ofLinearMap (e := e)
      ((refinedIdeal d f g).mkQ.comp (leftMulLinear ((f + lam * g) * d)))) := by
    rw [Hom.ofLinearMap_comp]
    change Hom.Epic (op ((f + lam * g) * d) • Hom.ofLinearMap (refinedIdeal d f g).mkQ)
    rw [show op ((f + lam * g) * d) • Hom.ofLinearMap (e := e)
        (refinedIdeal d f g).mkQ =
      (0 + op ((f + lam * g) * d) • Hom.ofLinearMap (refinedIdeal d f g).mkQ) by rw [zero_add],
      test_pencil_identity _ _ _ _ _ _ hlam, zero_add]
    change Hom.Epic (Hom.comp (Hom.ofLinearMap (refinedIdeal d f g).mkQ)
      (Hom.ofLinearMap (Section.leftMul (f * d))) +
      op lam • Hom.comp (Hom.ofLinearMap (refinedIdeal d f g).mkQ)
        (Hom.ofLinearMap (Section.leftMul (g * d))))
    simpa only [← Hom.ofLinearMap_comp, Section.leftMul, leftMulLinear, lam] using hep
  have hs := (quotient_section_epic_iff _ _).mp hp
  have hideal : refinedIdeal d f g ⊔ principalRightIdeal ((f + lam * g) * d) =
      firstIdeal d (f + lam * g) := by
    apply le_antisymm
    · exact sup_le (refinedIdeal_le_pencil d f g lam hlam) le_sup_right
    · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  rwa [hideal] at hs

variable [IsDomain R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
variable {k : Type*} [Field k] [Infinite k] [Algebra k R]

/-- The uniform fixed-anchor induction invariant. `Small (e+1)` is `DevLE e`.
It carries all finite families of actual bounded torsion epic germ tests. -/
def AffineBound (d : R) (e : ℕ) : Prop :=
  ∀ (a : R), a ≠ 0 → ∀ (B : R) {ι : Type u} [Fintype ι]
    (tests : ι → EpicGermTest R),
    ∃ H : R, Module.Small Rᵐᵒᵖ e (R ⧸ firstIdeal d (B + H * a)) ∧
      ∀ i, (tests i).Satisfied (B + H * a)

include k in
/-- Source selection establishes `P₀(d)` with the original quotient bound. -/
theorem affineBound_initial {d : R} {N : ℕ}
    (hd : Module.DevLE Rᵐᵒᵖ N (R ⧸ anchor d)) : AffineBound d (N + 1) := by
  intro a ha B ι _ tests
  obtain ⟨H, hH⟩ := exists_affine_epic_tests (k := k)
    (fun i => (tests i).level) (fun i => (tests i).Target)
    (fun i => (tests i).bounded) (fun i => (tests i).torsion)
    (fun i => (tests i).q) (fun i => (tests i).offset) (fun i => (tests i).epic)
    (fun i => (tests i).tail) (fun i => (tests i).tail_ne) ha B
  exact ⟨H, quotient_devLE hd _ le_sup_left, hH⟩

/-- The canonical test appended only to the second recursive call. -/
def canonicalTest {d : R} (hd : d ≠ 0) (f : R) (e : ℕ)
    (hI : Module.DevLE Rᵐᵒᵖ e (R ⧸ firstIdeal d f)) : EpicGermTest R where
  level := e
  Target := R ⧸ firstIdeal d f
  bounded := hI
  torsion := quotient_isTorsion_of_principal_le
    (OreRightIntersection.rightOreCondition_of_isNoetherian (R := R))
    d hd (firstIdeal d f) le_sup_left
  q := Hom.ofLinearMap (firstIdeal d f).mkQ
  offset := 0
  epic := Hom.epic_ofLinearMap_of_surjective _ (Submodule.mkQ_surjective _)
  tail := d
  tail_ne := hd

include k in
/-- The two-call step `P_h(d) → P_(h+1)(d)`, lowering `DevLE e` to
`Small e`, with the same anchor and every old test preserved. -/
theorem affineBound_step {d : R} (hd : d ≠ 0) (e : ℕ)
    (hbound : AffineBound d (e + 1)) : AffineBound d e := by
  classical
  intro a ha B ι _ tests
  obtain ⟨H, hI, htests⟩ := hbound a ha B tests
  let f := B + H * a
  obtain ⟨T, C₀, hT, hrel₀, hL, ha', hrel, hrec⟩ := recursion_data hd ha f
  let L := T * a * d
  let C := C₀ * a * d
  let a' := a * d * T * a
  let tests₂ : PUnit.{u + 1} → EpicGermTest R := fun _ => canonicalTest hd f e hI
  obtain ⟨H₂, hQ, htest₂⟩ := hbound a' ha' 0 tests₂
  let g := H₂ * a
  have hrec₂ := hrec H₂
  have hQ' : Module.DevLE Rᵐᵒᵖ e (R ⧸ secondIdeal d g L) := by
    change Module.DevLE Rᵐᵒᵖ e (R ⧸ firstIdeal d (0 + H₂ * (a * d * T * a))) at hQ
    rw [zero_add] at hQ
    rw [hrec₂.2] at hQ
    exact hQ
  have htest : Hom.Epic (Hom.ofLinearMap (e := e)
      ((firstIdeal d f).mkQ.comp (leftMulLinear (g * d * L)))) := by
    have ht := htest₂ PUnit.unit
    change Hom.Epic (e := e) (0 + op ((0 + H₂ * a') * d) •
      Hom.ofLinearMap (firstIdeal d f).mkQ) at ht
    rw [zero_add, zero_add, hrec₂.1] at ht
    change Hom.Epic (Hom.comp (Hom.ofLinearMap (firstIdeal d f).mkQ)
      (Hom.ofLinearMap (Section.leftMul (g * d * L)))) at ht
    simpa only [← Hom.ofLinearMap_comp, Section.leftMul, leftMulLinear] using ht
  have hW := refined_devLE e d f g L C hrel hI hQ'
  have hbad := secondCall_small_finite (k := k) d f g L C hrel hW htest
  have hold : (⋃ i, {c : k | ¬ (tests i).Satisfied (f + algebraMap k R c * g)}).Finite :=
    Set.finite_iUnion fun i => (tests i).pencil_finite (htests i) g
  obtain ⟨c, hc⟩ := (hbad.union hold).exists_notMem
  have hsmall : Module.Small Rᵐᵒᵖ e
      (R ⧸ firstIdeal d (f + algebraMap k R c * g)) := by
    by_contra hn
    exact hc (Set.mem_union_left _ hn)
  have hkeep : ∀ i, (tests i).Satisfied (f + algebraMap k R c * g) := by
    intro i
    by_contra hn
    exact hc (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨i, hn⟩))
  have heq : f + algebraMap k R c * g = B + (H + algebraMap k R c * H₂) * a :=
    affine_update B H H₂ a _
  rw [heq] at hsmall hkeep
  exact ⟨H + algebraMap k R c * H₂, hsmall, hkeep⟩

end GeneralizedStafford.FixedAnchor
