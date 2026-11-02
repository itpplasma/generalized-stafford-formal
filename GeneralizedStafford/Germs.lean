module

public import GeneralizedStafford.Basic
public import AlgebraicAnalysis.Module.DualSeparationGeneral
public import Mathlib.Algebra.Algebra.Opposite

@[expose] public section

/-!
# Germs and source selection

The Gabriel quotient `F_e` and its germs are represented concretely by the
germ calculus of `AlgebraicAnalysis.Module.Germ`: a germ of level `e` of a
module `X` is an element of `Section R e X = Hom Rᵐᵒᵖ e R X`, i.e. a partial
map from a submodule of `R` with small cokernel, modulo maps that agree on a
dense submodule; `Hom.Epic w` is "`w` is epic modulo `Kdim < e`".

* **Central scalars.** A central `λ ∈ k` acts on sections of a critical
  module through the centre of its Schur division ring
  (`section_central_scalar`).
* **Unit germs.** `q_J r` is epic iff `Kdim R/(J + rR) < e`
  (`smul_mkQ_epic_iff`).
* **Epic criterion, pencils and pencil stability.** An epic
  germ `v` stays epic along `v + u λ` for all but finitely many `λ`
  (`germ_pencil_finite`).
* **Escape and maximal rank.** These are
  `AlgebraicAnalysis.Goldie.IsGoldieTorsion.exists_smul_mul_not_mem` and
  `IsGoldieTorsion.exists_injective_right_mul`; together with the pencil lemma
  they give finite affine source selection in Goldie-torsion bimodules
  (`exists_affine_source_of_goldie`).
* **Source selection.** A *test* (`GermTest`) is
  `(e, V, q, z, c)` with `q` an epic germ and `c` regular; `f` satisfies it if
  `z + q f c` is epic. Every finite family of tests is satisfied by some
  `f = x + H t` (`GermTest.exists_affine_satisfied`), and a satisfied test stays
  satisfied along `f + λ g` for almost all `λ` (`GermTest.pencil_finite`).
-/

namespace GeneralizedStafford

open Module Module.Germ MulOpposite nonZeroDivisors
open AlgebraicAnalysis AlgebraicAnalysis.Goldie AlgebraicAnalysis.TorsionEscape
open AlgebraicAnalysis.DenominatorTorsion

universe u v

/-! ## Central scalars -/

section CentralScalars

variable {R : Type u} [Ring R] {C : Type v} [AddCommGroup C] [Module Rᵐᵒᵖ C] {e : ℕ}

/-- A central field `k` of `R`, viewed in the centre of `Rᵐᵒᵖ`. -/
def oppositeCentralField (k : Type*) [Field k] [Algebra k R] : k →+* Subring.center Rᵐᵒᵖ :=
  (algebraMap k Rᵐᵒᵖ).codRestrict _ (fun c =>
    Subring.mem_center_iff.mpr fun r => (Algebra.commutes c r).symm)

/-- Right multiplication of a section by a central scalar `λ` is the left
action of the Schur endomorphism `φ_λ` , also for germs defined only on a dense submodule. -/
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

end CentralScalars

/-! ## Unit germs -/

section UnitGerms

variable {R : Type u} [Ring R] [IsNoetherian Rᵐᵒᵖ R] {e : ℕ}

/-- The germ of `R → R/J, r ↦ x r + J` is epic iff `Kdim R/(J + xR) < e`. -/
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

/-- **Unit germs.** For the unit germ `q_J` of `R/J` and `x ∈ R`,
the germ `q_J x` is epic iff `Kdim R/(J + xR) < e`. -/
theorem smul_mkQ_epic_iff (J : Submodule Rᵐᵒᵖ R) (x : R) :
    Hom.Epic (op x • Hom.ofLinearMap (e := e) J.mkQ) ↔
      Module.Small Rᵐᵒᵖ e (R ⧸ (J ⊔ principalRightIdeal x)) := by
  rw [← quotient_section_epic_iff]
  have he : op x • Hom.ofLinearMap (e := e) J.mkQ =
      Hom.ofLinearMap (e := e) (J.mkQ.comp (leftMulLinear x)) := by
    change Hom.comp (Hom.ofLinearMap J.mkQ) (Hom.ofLinearMap (Section.leftMul x)) = _
    rw [← Hom.ofLinearMap_comp]
    rfl
  rw [he]

end UnitGerms

/-! ## Pencil stability -/

section Stability

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]
  [IsNoetherian Rᵐᵒᵖ M] {k : Type*} [Field k] [Algebra k R] {e : ℕ}

/-- **Pencil stability.** If `v` is an epic germ of a module `M` with
`Kdim M ≤ e` and `u` is any germ, then `v + u λ` is epic for all but finitely
many `λ ∈ k`. Proof: by the epic criterion it suffices to test the
finitely many critical top factors `C` of a critical filtration; on each,
`h ↦ h(v + u λ) = P_v h + φ_λ P_u h` is a central pencil with `P_v` injective,
so it is injective for almost all `λ`. -/
theorem germ_pencil_finite (hM : Module.DevLE Rᵐᵒᵖ e M)
    (F : Module.CriticalFiltration Rᵐᵒᵖ e M) (v u : Section R e M) (hv : Hom.Epic v) :
    {c : k | ¬ Hom.Epic (v + op (algebraMap k R c) • u)}.Finite := by
  classical
  have hfin : (⋃ i : F.TopIndex,
      {c : k | ¬ Function.Injective (fun h : Hom Rᵐᵒᵖ e M (F.TopFactor i) =>
        Hom.comp h (v + op (algebraMap k R c) • u))}).Finite := by
    refine Set.finite_iUnion fun i => ?_
    let := End.divisionRing (F.topFactor_critical i)
    let := Hom.finite_of_devLE hM (F.topFactor_critical i)
    let κ : k →+* End Rᵐᵒᵖ e (F.TopFactor i) :=
      End.centralMap.comp (oppositeCentralField (R := R) k)
    have hκ : ∀ c x, κ c * x = x * κ c := fun c x =>
      (End.centralMap_commute (oppositeCentralField (R := R) k c) x).eq
    refine (centralPencil_injective_finite κ hκ (Hom.precompLinear v)
      (Hom.precompLinear u) (fun h h' he => hv.right_cancel h h' he)).subset ?_
    intro c hc hinj
    apply hc
    have heq : (fun h : Hom Rᵐᵒᵖ e M (F.TopFactor i) =>
        Hom.comp h (v + op (algebraMap k R c) • u)) =
        centralPencil κ hκ (Hom.precompLinear v) (Hom.precompLinear u) c := by
      funext h
      rw [Hom.comp_add]
      change Hom.comp h v + Hom.comp h (Hom.comp u (Hom.ofLinearMap
          (Section.leftMul (algebraMap k R c)))) = Hom.comp h v + κ c • Hom.comp h u
      rw [← Hom.comp_assoc]
      exact congrArg (Hom.comp h v + ·)
        (section_central_scalar (oppositeCentralField (R := R) k c) (Hom.comp h u))
    rw [heq]
    exact hinj
  refine hfin.subset fun c hc => ?_
  by_contra hn
  apply hc
  refine (Hom.epic_iff_injective_comp_topFactors hM F _).mpr fun i => ?_
  by_contra hi
  exact hn (Set.mem_iUnion.mpr ⟨i, hi⟩)

end Stability

/-! ## Affine selection in Goldie-torsion bimodules -/

section FiniteSelection

variable {R : Type*} [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
variable {ι k : Type*} [Field k] [Infinite k]
variable {Eᵢ Dᵢ Wᵢ : ι → Type*}
variable [∀ i, DivisionRing (Eᵢ i)]
variable [∀ i, AddCommGroup (Dᵢ i)] [∀ i, Module (Eᵢ i) (Dᵢ i)]
variable [∀ i, Module.Finite (Eᵢ i) (Dᵢ i)]
variable [∀ i, AddCommGroup (Wᵢ i)] [∀ i, Module (Eᵢ i) (Wᵢ i)]
variable [∀ i, Module Rᵐᵒᵖ (Wᵢ i)] [∀ i, SMulCommClass Rᵐᵒᵖ (Eᵢ i) (Wᵢ i)]

/-- Finite affine selection in Goldie-torsion bimodules, direction form
(Steps 1 and 2 below). Let `Pᵢ` be injective maps from finite-dimensional
spaces into Goldie-torsion bimodules `Wᵢ`, `Zᵢ` arbitrary, `a ≠ 0` and `bᵢ`
regular. There is a direction `H` such that `d ↦ Zᵢ d + Pᵢ(d) (B + σ(c) H a) bᵢ`
is injective for all `i` and all but finitely many central scalars `c`.
Step 1 combines maximal rank for each `i` by ordinary pencils
(AlgebraicAnalysis `exists_simultaneously_injective`); Step 2 is a reversed
pencil (AlgebraicAnalysis `reversed_centralPencil_injective_finite`). -/
theorem exists_affine_direction_of_goldie
    (hW : ∀ i, IsGoldieTorsion R (Wᵢ i))
    (σ : k →+* R) (κ : ∀ i, k →+* Eᵢ i)
    (hκ : ∀ i c a, κ i c * a = a * κ i c)
    (hscalar : ∀ i c (w : Wᵢ i), op (σ c) • w = κ i c • w)
    (P Z : ∀ i, Dᵢ i →ₗ[Eᵢ i] Wᵢ i) (hP : ∀ i, Function.Injective (P i))
    (s : Finset ι) (b : ι → R) (hb : ∀ i ∈ s, b i ∈ R⁰)
    {a : R} (ha : a ≠ 0) (B : R) :
    ∃ H : R, {c : k | ∃ i ∈ s, ¬ Function.Injective
      (fun d => Z i d + op ((B + σ c * H * a) * b i) • P i d)}.Finite := by
  classical
  let F (i : ι) (r : R) : Dᵢ i →ₗ[Eᵢ i] Wᵢ i :=
    (rightMulLinear (E := Eᵢ i) (r * (a * b i))).comp (P i)
  have hF (i : ι) (r t : R) (c : k) (d : Dᵢ i) :
      F i (r + σ c * t) d = F i r d + κ i c • F i t d := by
    change op ((r + σ c * t) * (a * b i)) • P i d =
      op (r * (a * b i)) • P i d + κ i c • (op (t * (a * b i)) • P i d)
    rw [add_mul, op_add, add_smul, mul_assoc]
    congr 1
    rw [op_mul, mul_smul, hscalar, smul_comm]
  obtain ⟨H, hH⟩ := exists_simultaneously_injective σ κ hκ F hF s (fun i hi =>
    (hW i).exists_injective_right_mul σ (κ i) (hκ i) (hscalar i)
      (P i) (hP i) (fun h0 => ha ((hb i hi).2 a h0)))
  let A (i : ι) : Dᵢ i →ₗ[Eᵢ i] Wᵢ i :=
    Z i + (rightMulLinear (E := Eᵢ i) (B * b i)).comp (P i)
  have hfinite : (⋃ i ∈ s,
      {c | ¬ Function.Injective (centralPencil (κ i) (hκ i) (A i) (F i H) c)}).Finite :=
    s.finite_toSet.biUnion fun i hi =>
      reversed_centralPencil_injective_finite (κ i) (hκ i) _ _ (hH i hi)
  refine ⟨H, hfinite.subset ?_⟩
  rintro c ⟨i, hi, hbad⟩
  refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, ?_⟩⟩
  have heq : (fun d => Z i d + op ((B + σ c * H * a) * b i) • P i d) =
      centralPencil (κ i) (hκ i) (A i) (F i H) c := by
    funext d
    change Z i d + op ((B + σ c * H * a) * b i) • P i d =
      (Z i d + op (B * b i) • P i d) + κ i c • (op (H * (a * b i)) • P i d)
    have hscaled : op (σ c * (H * (a * b i))) • P i d =
        κ i c • (op (H * (a * b i)) • P i d) := by
      rw [op_mul, mul_smul, hscalar, smul_comm]
    rw [add_mul, op_add, add_smul, mul_assoc, mul_assoc, hscaled]
    abel
  change ¬ Function.Injective (centralPencil (κ i) (hκ i) (A i) (F i H) c)
  rwa [← heq]

/-- Finite affine selection in Goldie-torsion bimodules: some `H` makes every
`d ↦ Zᵢ d + Pᵢ(d) (B + H a) bᵢ` injective (take `H := σ(c) H₀` for a good
central `c`). -/
theorem exists_affine_source_of_goldie
    (hW : ∀ i, IsGoldieTorsion R (Wᵢ i))
    (σ : k →+* R) (κ : ∀ i, k →+* Eᵢ i)
    (hκ : ∀ i c a, κ i c * a = a * κ i c)
    (hscalar : ∀ i c (w : Wᵢ i), op (σ c) • w = κ i c • w)
    (P Z : ∀ i, Dᵢ i →ₗ[Eᵢ i] Wᵢ i) (hP : ∀ i, Function.Injective (P i))
    (s : Finset ι) (b : ι → R) (hb : ∀ i ∈ s, b i ∈ R⁰)
    {a : R} (ha : a ≠ 0) (B : R) :
    ∃ H : R, ∀ i ∈ s, Function.Injective
      (fun d => Z i d + op ((B + H * a) * b i) • P i d) := by
  obtain ⟨H, hH⟩ := exists_affine_direction_of_goldie hW σ κ hκ hscalar P Z hP s b hb ha B
  obtain ⟨c, hc⟩ := hH.exists_notMem
  refine ⟨σ c * H, ?_⟩
  intro i hi
  by_contra hbad
  exact hc ⟨i, hi, hbad⟩

end FiniteSelection

/-! ## Tests -/

/-- A **test** `(e, V, q, z, c)`: a Noetherian
Goldie-torsion module `V` (the target) with `Kdim V ≤ e`, an epic germ `q`, an
arbitrary germ `z` (the offset) and a regular tail `c`. -/
structure GermTest (R : Type u) [Ring R] where
  /-- The level `e`. -/
  level : ℕ
  /-- The target module `V`. -/
  Target : Type u
  [addCommGroup : AddCommGroup Target]
  [module : Module Rᵐᵒᵖ Target]
  [noetherian : IsNoetherian Rᵐᵒᵖ Target]
  /-- `Kdim V ≤ e`. -/
  bounded : Module.DevLE Rᵐᵒᵖ level Target
  /-- `V` is Goldie-torsion. -/
  torsion : IsGoldieTorsion R Target
  /-- The epic germ `q`. -/
  q : Hom Rᵐᵒᵖ level R Target
  /-- The offset germ `z`. -/
  offset : Hom Rᵐᵒᵖ level R Target
  /-- `q` is epic. -/
  epic : Hom.Epic q
  /-- The tail `c`. -/
  tail : R
  /-- The tail `c` is regular. -/
  tail_reg : tail ∈ R⁰

attribute [instance] GermTest.addCommGroup GermTest.module GermTest.noetherian

section Tests

variable {R : Type u} [Ring R]

/-- An element `f` **satisfies** the test `(e, V, q, z, c)` if `z + q f c` is
epic. -/
def GermTest.Satisfied (τ : GermTest R) (f : R) : Prop :=
  Hom.Epic (τ.offset + op (f * τ.tail) • τ.q)

end Tests

/-! ## Source selection for germ tests -/

section Selection

variable {R : Type u} [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
variable {k : Type*} [Field k] [Infinite k] [Algebra k R]

include k in
/-- Source selection for finitely many critical germ tests: given epic germs
`qᵢ`, offsets `zᵢ`, regular tails `bᵢ`, `a ≠ 0` and `B`, some `H` makes every
`h ↦ h (zᵢ + qᵢ (B + H a) bᵢ)` injective on the Schur space of the
Goldie-torsion critical module `Cᵢ`. -/
theorem exists_affine_germ_tests
    {ι : Type*} [Fintype ι] (e : ι → ℕ) (M C : ι → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module Rᵐᵒᵖ (M i)]
    [∀ i, IsNoetherian Rᵐᵒᵖ (M i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module Rᵐᵒᵖ (C i)]
    [∀ i, IsNoetherian Rᵐᵒᵖ (C i)]
    (hM : ∀ i, Module.DevLE Rᵐᵒᵖ (e i) (M i))
    (hC : ∀ i, Module.Critical Rᵐᵒᵖ (e i) (C i))
    (ht : ∀ i, IsGoldieTorsion R (C i))
    (q z : ∀ i, Hom Rᵐᵒᵖ (e i) R (M i)) (hq : ∀ i, Hom.Epic (q i))
    (b : ι → R) (hb : ∀ i, b i ∈ R⁰) {a : R} (ha : a ≠ 0) (B : R) :
    ∃ H : R, ∀ i, Function.Injective
      (fun h : Hom Rᵐᵒᵖ (e i) (M i) (C i) =>
        Hom.comp h (z i + op ((B + H * a) * b i) • q i)) := by
  classical
  let : ∀ i, DivisionRing (End Rᵐᵒᵖ (e i) (C i)) := fun i => End.divisionRing (hC i)
  let : ∀ i, Module.Finite (End Rᵐᵒᵖ (e i) (C i))
      (Hom Rᵐᵒᵖ (e i) (M i) (C i)) := fun i => Hom.finite_of_devLE (hM i) (hC i)
  let κ (i : ι) : k →+* End Rᵐᵒᵖ (e i) (C i) :=
    End.centralMap.comp (oppositeCentralField (R := R) k)
  let P (i : ι) := Hom.precompLinear (C := C i) (q i)
  let Z (i : ι) := Hom.precompLinear (C := C i) (z i)
  obtain ⟨H, hH⟩ := exists_affine_source_of_goldie
    (fun i => isGoldieTorsion_section (hC i) (ht i))
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

include k in
/-- **Source selection, epic form.** For finitely many
Goldie-torsion modules `Mᵢ` with `Kdim Mᵢ ≤ eᵢ`, epic germs `qᵢ`, offsets `zᵢ`
and regular tails `bᵢ`, and for `a ≠ 0` and `B`, some `H` makes every germ
`zᵢ + qᵢ (B + H a) bᵢ` epic. By the epic criterion it suffices to
satisfy the critical tests of the finitely many top factors. -/
theorem exists_affine_epic_tests
    {ι : Type*} [Fintype ι] (e : ι → ℕ) (M : ι → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module Rᵐᵒᵖ (M i)]
    [∀ i, IsNoetherian Rᵐᵒᵖ (M i)]
    (hM : ∀ i, Module.DevLE Rᵐᵒᵖ (e i) (M i))
    (ht : ∀ i, IsGoldieTorsion R (M i))
    (q z : ∀ i, Hom Rᵐᵒᵖ (e i) R (M i)) (hq : ∀ i, Hom.Epic (q i))
    (b : ι → R) (hb : ∀ i, b i ∈ R⁰) {a : R} (ha : a ≠ 0) (B : R) :
    ∃ H : R, ∀ i, Hom.Epic (z i + op ((B + H * a) * b i) • q i) := by
  classical
  let F (i : ι) : Module.CriticalFiltration Rᵐᵒᵖ (e i) (M i) :=
    Classical.choice (hM i).nonempty_criticalFiltration
  let J := (i : ι) × (F i).TopIndex
  let C (j : J) := (F j.1).TopFactor j.2
  have hC (j : J) : Module.Critical Rᵐᵒᵖ (e j.1) (C j) :=
    (F j.1).topFactor_critical j.2
  have htC (j : J) : IsGoldieTorsion R (C j) := by
    let U := (F j.1).toRelSeries j.2.val.succ
    let V := ((F j.1).toRelSeries j.2.val.castSucc).comap U.subtype
    exact IsGoldieTorsion.of_surjective V.mkQ V.mkQ_surjective
      (IsGoldieTorsion.of_injective U.subtype Subtype.val_injective (ht j.1))
  obtain ⟨H, hH⟩ := exists_affine_germ_tests (k := k)
    (fun j : J => e j.1) (fun j => M j.1) C
    (fun j => hM j.1) hC htC (fun j => q j.1) (fun j => z j.1)
    (fun j => hq j.1) (fun j => b j.1) (fun j => hb j.1) ha B
  exact ⟨H, fun i => (Hom.epic_iff_injective_comp_topFactors (hM i) (F i) _).mpr
    (fun j => hH ⟨i, j⟩)⟩

end Selection

/-! ## Tests: stability, selection and the unit test -/

section TestLemmas

variable {R : Type u} [Ring R]

/-- For a central `λ`: `z + q (f + λ g) c = (z + q f c) + (q g c) λ`. -/
theorem test_pencil_identity {M : Type u} [AddCommGroup M] [Module Rᵐᵒᵖ M]
    {e : ℕ} (q z : Section R e M) (f g b lam : R)
    (hlam : ∀ x : R, lam * x = x * lam) :
    z + op ((f + lam * g) * b) • q =
      (z + op (f * b) • q) + op lam • (op (g * b) • q) := by
  have he : (f + lam * g) * b = f * b + (g * b) * lam := by
    rw [add_mul, mul_assoc, hlam]
  rw [he, op_add, add_smul, ← add_assoc, Section.right_action_assoc]

/-- **Stability for tests.** If `f` satisfies a test, then so does
`f + λ g` for all but finitely many central `λ ∈ k`. -/
theorem GermTest.pencil_finite {k : Type*} [Field k] [Algebra k R]
    (τ : GermTest R) {f : R} (hf : τ.Satisfied f) (g : R) :
    {c : k | ¬ τ.Satisfied (f + algebraMap k R c * g)}.Finite := by
  classical
  let F := Classical.choice τ.bounded.nonempty_criticalFiltration
  have hfin := germ_pencil_finite (k := k) τ.bounded F
    (τ.offset + op (f * τ.tail) • τ.q) (op (g * τ.tail) • τ.q) hf
  simpa only [GermTest.Satisfied,
    test_pencil_identity _ _ _ _ _ _ (fun x => (Algebra.commutes _ x))] using hfin

/-- **Selection for tests.** Assume (S), (N), (Z). For every `x`,
every `t ≠ 0` and every finite family of tests, some `f = x + H t` satisfies
all of them. -/
theorem GermTest.exists_affine_satisfied [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    (k : Type*) [Field k] [Infinite k] [Algebra k R]
    {ι : Type*} [Fintype ι] (tests : ι → GermTest R) (x : R) {t : R} (ht : t ≠ 0) :
    ∃ H : R, ∀ i, (tests i).Satisfied (x + H * t) :=
  exists_affine_epic_tests (k := k)
    (fun i => (tests i).level) (fun i => (tests i).Target)
    (fun i => (tests i).bounded) (fun i => (tests i).torsion)
    (fun i => (tests i).q) (fun i => (tests i).offset) (fun i => (tests i).epic)
    (fun i => (tests i).tail) (fun i => (tests i).tail_reg) ht x

/-- The **unit test** `(e, R/J, q_J, 0, 1)` of a Goldie-torsion quotient `R/J`
with `Kdim R/J ≤ e`. -/
def unitTest [IsNoetherian Rᵐᵒᵖ R] (J : Submodule Rᵐᵒᵖ R) (e : ℕ)
    (hJ : Module.DevLE Rᵐᵒᵖ e (R ⧸ J)) (hT : IsGoldieTorsion R (R ⧸ J)) :
    GermTest R where
  level := e
  Target := R ⧸ J
  bounded := hJ
  torsion := hT
  q := Hom.ofLinearMap J.mkQ
  offset := 0
  epic := Hom.epic_ofLinearMap_of_surjective _ (Submodule.mkQ_surjective _)
  tail := 1
  tail_reg := Submonoid.one_mem _

/-- `f` satisfies the unit test of `R/J` iff `Kdim R/(J + fR) < e`. -/
theorem unitTest_satisfied_iff [IsNoetherian Rᵐᵒᵖ R] (J : Submodule Rᵐᵒᵖ R) (e : ℕ)
    (hJ : Module.DevLE Rᵐᵒᵖ e (R ⧸ J)) (hT : IsGoldieTorsion R (R ⧸ J)) (f : R) :
    (unitTest J e hJ hT).Satisfied f ↔
      Module.Small Rᵐᵒᵖ e (R ⧸ (J ⊔ principalRightIdeal f)) := by
  change Hom.Epic (0 + op (f * 1) • Hom.ofLinearMap (e := e) J.mkQ) ↔ _
  rw [zero_add, mul_one]
  exact smul_mkQ_epic_iff J f

end TestLemmas

end GeneralizedStafford
