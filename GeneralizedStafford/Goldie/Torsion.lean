module

public import GeneralizedStafford.Goldie.Basic
public import AlgebraicAnalysis.Module.TorsionEscape
public import AlgebraicAnalysis.Module.GermSchur

@[expose] public section

/-!
# Goldie torsion, regular common annihilators and escape

`IsGoldieTorsion R M` is convention C4 of `docs/core-theorem.md`: every
element of the right module `M` is killed by a regular element. Over a simple
right Noetherian ring this class has common regular annihilators for finitely
many elements (input I1), and the escape lemma (Lemma 3.4) and finite affine
source selection hold with nonzero, possibly singular, right tails `a` and
regular test tails `bᵢ`.

The linear-algebra steps (`exists_injective_of_escape`,
`exists_simultaneously_injective`, central pencils) are reused unchanged from
`AlgebraicAnalysis.TorsionEscape`; only the torsion inputs change.
-/

namespace GeneralizedStafford.Goldie

open MulOpposite nonZeroDivisors
open AlgebraicAnalysis AlgebraicAnalysis.TorsionEscape AlgebraicAnalysis.DenominatorTorsion

universe u v

/-- A right module is Goldie-torsion if every element is killed by a regular
element (convention C4). -/
def IsGoldieTorsion (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] :
    Prop :=
  ∀ m : M, ∃ s ∈ R⁰, op s • m = 0

section Closure

variable {R : Type u} [Ring R]
variable {M N : Type*} [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup N] [Module Rᵐᵒᵖ N]

theorem IsGoldieTorsion.of_injective (f : M →ₗ[Rᵐᵒᵖ] N) (hf : Function.Injective f)
    (hN : IsGoldieTorsion R N) : IsGoldieTorsion R M := fun m => by
  obtain ⟨s, hs, hsm⟩ := hN (f m)
  exact ⟨s, hs, hf (by rw [map_smul, hsm, map_zero])⟩

theorem IsGoldieTorsion.of_surjective (f : M →ₗ[Rᵐᵒᵖ] N) (hf : Function.Surjective f)
    (hM : IsGoldieTorsion R M) : IsGoldieTorsion R N := fun n => by
  obtain ⟨m, rfl⟩ := hf n
  obtain ⟨s, hs, hsm⟩ := hM m
  exact ⟨s, hs, by rw [← map_smul, hsm, map_zero]⟩

/-- Goldie torsion is ordinary torsion (regular elements are nonzero). -/
theorem IsGoldieTorsion.isTorsionRight [Nontrivial R] (hM : IsGoldieTorsion R M) :
    IsTorsionRight (R := R) (M := M) := fun m => by
  obtain ⟨s, hs, hsm⟩ := hM m
  exact ⟨s, nonZeroDivisors.ne_zero hs, hsm⟩

/-- Over a domain, ordinary torsion is Goldie torsion. -/
theorem isGoldieTorsion_of_isTorsionRight [IsDomain R]
    (hM : IsTorsionRight (R := R) (M := M)) : IsGoldieTorsion R M := fun m => by
  obtain ⟨s, hs, hsm⟩ := hM m
  exact ⟨s, mem_nonZeroDivisors_of_ne_zero hs, hsm⟩

/-- A quotient `R/I` with `I` containing a regular element is Goldie-torsion
(input I1). -/
theorem isGoldieTorsion_quotient [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    {I : Submodule Rᵐᵒᵖ R} {s : R} (hsI : s ∈ I) (hs : s ∈ R⁰) :
    IsGoldieTorsion R (R ⧸ I) := fun z => by
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective I z
  obtain ⟨b, hb, hfb⟩ := exists_mul_mem_of_mem_nonZeroDivisors hsI hs f
  refine ⟨b, hb, ?_⟩
  rw [← map_smul]
  exact (Submodule.Quotient.mk_eq_zero I).mpr hfb

end Closure

section Escape

variable {R E W : Type*} [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R] [DivisionRing E]
variable [AddCommGroup W] [Module Rᵐᵒᵖ W] [Module E W]
variable [SMulCommClass Rᵐᵒᵖ E W]

/-- A finite-dimensional subspace of a Goldie-torsion bimodule has a common
regular right annihilator (input I1). -/
theorem exists_common_regular_annihilator (hW : IsGoldieTorsion R W)
    (Y : Submodule E W) [Module.Finite E Y] :
    ∃ c ∈ R⁰, ∀ y ∈ Y, op c • y = 0 := by
  classical
  let B := Module.finBasis E Y
  obtain ⟨c, hc, hcB⟩ := exists_mem_nonZeroDivisors_finset Finset.univ
    (fun i => rightAnnihilator (R := R) (B i : W))
    (fun i _ => by
      obtain ⟨r, hr, hri⟩ := hW (B i : W)
      exact ⟨r, hri, hr⟩)
  refine ⟨c, hc, ?_⟩
  intro y hy
  have heq := congrArg (fun z : Y => (z : W)) (B.sum_repr ⟨y, hy⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at heq
  rw [← heq, Finset.smul_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [smul_comm, show op c • (B i : W) = 0 from hcB i (Finset.mem_univ i), smul_zero]

/-- **Escape (Lemma 3.4).** In a Goldie-torsion bimodule over a simple right
Noetherian ring, for `g ≠ 0` and `t' ≠ 0` (possibly singular), `g R t'` is
not contained in any finite-dimensional left subspace. -/
theorem exists_smul_mul_not_mem_of_goldie (hW : IsGoldieTorsion R W)
    {g : W} (hg : g ≠ 0) {b : R} (hb : b ≠ 0)
    (Y : Submodule E W) [Module.Finite E Y] :
    ∃ r : R, op (r * b) • g ∉ Y := by
  classical
  by_contra! h
  obtain ⟨c, hc, hcY⟩ := exists_common_regular_annihilator hW Y
  have hbc : b * c ∈ cyclicAnnihilator g := by
    simp only [cyclicAnnihilator, TwoSidedIdeal.mem_mk', Set.mem_ofPred_eq]
    intro r
    rw [← mul_assoc, op_mul, mul_smul]
    exact hcY _ (h r)
  have hbc0 : b * c ≠ 0 := fun h0 => hb (hc.2 b h0)
  have h1 := IsSimpleRing.one_mem_of_ne_zero_mem (cyclicAnnihilator g) hbc0 hbc
  have hzero := h1 1
  exact hg (by simpa using hzero)

variable {k D : Type*} [Field k] [Infinite k]
variable [AddCommGroup D] [Module E D] [Module.Finite E D]

/-- A finite-dimensional injective map into a Goldie-torsion bimodule stays
injective after right multiplication by `r b` for some `r`, for any `b ≠ 0`. -/
theorem exists_injective_right_mul_of_goldie (hW : IsGoldieTorsion R W)
    (σ : k →+* R) (κ : k →+* E) (hκ : ∀ c a, κ c * a = a * κ c)
    (hscalar : ∀ c (w : W), op (σ c) • w = κ c • w)
    (P : D →ₗ[E] W) (hP : Function.Injective P) {b : R} (hb : b ≠ 0) :
    ∃ r : R, Function.Injective ((rightMulLinear (E := E) (r * b)).comp P) := by
  apply exists_injective_of_escape σ κ hκ
    (fun r => (rightMulLinear (E := E) (r * b)).comp P)
  · intro r s c d
    change op ((r + σ c * s) * b) • P d =
      op (r * b) • P d + κ c • (op (s * b) • P d)
    rw [add_mul, op_add, add_smul, mul_assoc]
    congr 1
    rw [op_mul, mul_smul, hscalar, smul_comm]
  · intro d hd Y hY
    let := hY
    exact exists_smul_mul_not_mem_of_goldie hW
      (fun h => hd (hP (h.trans (map_zero P).symm))) hb Y

end Escape

section FiniteSelection

variable {R : Type*} [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
variable {ι k : Type*} [Field k] [Infinite k]
variable {Eᵢ Dᵢ Wᵢ : ι → Type*}
variable [∀ i, DivisionRing (Eᵢ i)]
variable [∀ i, AddCommGroup (Dᵢ i)] [∀ i, Module (Eᵢ i) (Dᵢ i)]
variable [∀ i, Module.Finite (Eᵢ i) (Dᵢ i)]
variable [∀ i, AddCommGroup (Wᵢ i)] [∀ i, Module (Eᵢ i) (Wᵢ i)]
variable [∀ i, Module Rᵐᵒᵖ (Wᵢ i)] [∀ i, SMulCommClass Rᵐᵒᵖ (Eᵢ i) (Wᵢ i)]

/-- Finite affine source selection in Goldie-torsion bimodules: a direction
`H` with only finitely many bad central scalars for the sources
`B + σ(c) H a`, with right tails `a bᵢ` (`a ≠ 0`, `bᵢ` regular). -/
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
    exists_injective_right_mul_of_goldie (hW i) σ (κ i) (hκ i) (hscalar i)
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

/-- The actual source `B + H a` supplied by finite affine selection in
Goldie-torsion bimodules. -/
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

section Section

open Module Module.Germ

variable {R : Type u} [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R] {e : ℕ}
variable {C : Type v} [AddCommGroup C] [Module Rᵐᵒᵖ C] [IsNoetherian Rᵐᵒᵖ C]

/-- Goldie torsion passes from a critical module to its section module: the
annihilator of a section is essential, hence contains a regular element
(Goldie). -/
theorem section_isGoldieTorsion (hC : Critical Rᵐᵒᵖ e C) (ht : IsGoldieTorsion R C) :
    IsGoldieTorsion R (Section R e C) := by
  intro w
  have hess : IsEssential (rightAnnihilator (R := R) w) := by
    intro y hy
    by_cases hyw : op y • w = 0
    · refine ⟨1, by rwa [mul_one], ?_⟩
      change op (y * 1) • w = 0
      rwa [mul_one]
    obtain ⟨i, c, hc, he⟩ := Section.exists_smul_eq_ofElement hC (op y • w) hyw
    rw [Section.right_action_assoc] at he
    obtain ⟨s, hs, hsc⟩ := ht c
    have hyi : y * i ≠ 0 := by
      intro h0
      rw [h0, op_zero, zero_smul] at he
      exact hc (Section.ofElement_injective hC (he.symm.trans (map_zero _).symm))
    refine ⟨i * s, fun h0 => hyi (hs.2 _ (by rwa [← mul_assoc] at h0)), ?_⟩
    change op (y * (i * s)) • w = 0
    rw [← mul_assoc, ← Section.right_action_assoc, he, ← map_smul, hsc, map_zero]
  obtain ⟨s, hsw, hs⟩ := exists_mem_nonZeroDivisors_of_isEssential hess
  exact ⟨s, hs, hsw⟩

end Section

end GeneralizedStafford.Goldie
