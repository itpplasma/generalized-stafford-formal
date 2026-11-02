module

public import AlgebraicAnalysis.RingTheory.Goldie.Torsion

@[expose] public section

/-!
# Finite affine source selection in Goldie-torsion bimodules

The Goldie-torsion class, common regular annihilators, escape (Lemma 3.4) and
maximal rank (Lemma 3.5) are in `AlgebraicAnalysis.RingTheory.Goldie.Torsion`.
This file adds the finite affine selection used for Lemma 3.6.
-/

namespace GeneralizedStafford.Goldie

open MulOpposite nonZeroDivisors
open AlgebraicAnalysis AlgebraicAnalysis.Goldie AlgebraicAnalysis.TorsionEscape

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

end GeneralizedStafford.Goldie
