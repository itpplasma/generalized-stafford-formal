module

public import Mathlib.Algebra.Module.Opposite
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.RingTheory.Finiteness.Defs

@[expose] public section

/-!
# Left statements from right statements

For a ring `A` with an anti-automorphism `τ : A ≃+* Aᵐᵒᵖ`, the map
`I ↦ {y | τ⁻¹(op y) ∈ I}` is a bijection from left ideals of `A` to right ideals
of `A`, and a left `A`-module is a right `A`-module through `τ`. Hence a
statement about right ideals and right modules of `A` yields the same statement
for left ideals and left modules, with no extra hypothesis on `A`.

The results here are generic: they take the right-hand statement as a
hypothesis. The two-generator transfer is used for the Weyl algebra in
`GeneralizedStafford.Weyl`.
-/

universe u v

namespace GeneralizedStafford

open MulOpposite

section Left

variable {A : Type u} [Ring A]

/-- The right ideal `τ(I)` attached to a left ideal `I` by the anti-automorphism
`τ`: `y ∈ τ(I)` iff `τ⁻¹(op y) ∈ I`. -/
def leftToRight (τ : A ≃+* Aᵐᵒᵖ) (I : Submodule A A) : Submodule Aᵐᵒᵖ A where
  carrier := {y | τ.symm (op y) ∈ I}
  add_mem' {x y} hx hy := by
    change τ.symm (op (x + y)) ∈ I
    rw [op_add, map_add]
    exact I.add_mem hx hy
  zero_mem' := by
    change τ.symm (op 0) ∈ I
    simp
  smul_mem' r y hy := by
    change τ.symm (op (y * r.unop)) ∈ I
    rw [op_mul, map_mul]
    exact I.smul_mem _ hy

/-- A left ideal with two generators, from the two-generator statement for right
ideals. -/
theorem twoGeneratedLeft_of_right (τ : A ≃+* Aᵐᵒᵖ)
    (hR : ∀ J : Submodule Aᵐᵒᵖ A, ∃ a b : A, J = Submodule.span Aᵐᵒᵖ {a, b})
    (I : Submodule A A) : ∃ a b : A, I = Submodule.span A {a, b} := by
  obtain ⟨a, b, hab⟩ := hR (leftToRight τ I)
  refine ⟨τ.symm (op a), τ.symm (op b), ?_⟩
  ext x
  have hx : x ∈ I ↔ unop (τ x) ∈ leftToRight τ I := by
    change x ∈ I ↔ τ.symm (op (unop (τ x))) ∈ I
    simp
  rw [hx, hab, Submodule.mem_span_pair, Submodule.mem_span_pair]
  constructor
  · rintro ⟨r, s, hrs⟩
    refine ⟨τ.symm r, τ.symm s, ?_⟩
    apply τ.injective
    apply unop_injective
    simp only [smul_eq_mul, map_add, map_mul, RingEquiv.apply_symm_apply, unop_add,
      unop_mul, unop_op, ← hrs, MulOpposite.smul_eq_mul_unop]
  · rintro ⟨r, s, hrs⟩
    refine ⟨τ r, τ s, ?_⟩
    rw [← hrs]
    simp only [smul_eq_mul, map_add, map_mul, RingEquiv.apply_symm_apply, unop_add,
      unop_mul, unop_op, MulOpposite.smul_eq_mul_unop]

theorem mem_leftToRight (τ : A ≃+* Aᵐᵒᵖ) (I : Submodule A A) (x : A) :
    unop (τ x) ∈ leftToRight τ I ↔ x ∈ I := by
  change τ.symm (op (unop (τ x))) ∈ I ↔ x ∈ I
  simp

/-- The transfer `I ↦ τ(I)` is injective. -/
theorem leftToRight_injective (τ : A ≃+* Aᵐᵒᵖ) :
    Function.Injective (leftToRight τ) := by
  intro I I' h
  ext x
  rw [← mem_leftToRight τ I, ← mem_leftToRight τ I', h]

/-- The transfer of a left span is the right span of the transferred generators. -/
theorem leftToRight_span (τ : A ≃+* Aᵐᵒᵖ) (S : Set A) :
    leftToRight τ (Submodule.span A S) =
      Submodule.span Aᵐᵒᵖ ((fun x => unop (τ x)) '' S) := by
  apply le_antisymm
  · intro y hy
    have hy' : τ.symm (op y) ∈ Submodule.span A S := hy
    have key : ∀ z ∈ Submodule.span A S,
        unop (τ z) ∈ Submodule.span Aᵐᵒᵖ ((fun x => unop (τ x)) '' S) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
      | zero => simp
      | add z w _ _ hz hw => simpa using Submodule.add_mem _ hz hw
      | smul r z _ hz =>
        have := Submodule.smul_mem _ (τ r) hz
        simpa [smul_eq_mul, MulOpposite.smul_eq_mul_unop] using this
    simpa using key _ hy'
  · rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact (mem_leftToRight τ _ z).2 (Submodule.subset_span hz)

/-- Prescribed first generator for left ideals, from the right statement. -/
theorem prescribedTwoGeneratedLeft_of_right (τ : A ≃+* Aᵐᵒᵖ)
    (hR : ∀ (J : Submodule Aᵐᵒᵖ A) (a : A), a ∈ J → a ≠ 0 → ∀ y ∈ J, ∀ t : A, t ≠ 0 →
      ∃ h ∈ J, J = Submodule.span Aᵐᵒᵖ {a} ⊔ Submodule.span Aᵐᵒᵖ {y + h * t})
    (I : Submodule A A) (a : A) (haI : a ∈ I) (ha : a ≠ 0) (y : A) (hy : y ∈ I)
    (t : A) (ht : t ≠ 0) :
    ∃ h ∈ I, I = Submodule.span A {a} ⊔ Submodule.span A {y + t * h} := by
  have hne : ∀ z : A, z ≠ 0 → unop (τ z) ≠ 0 := fun z hz h0 =>
    hz (τ.injective (by simpa using congrArg op h0))
  obtain ⟨h', hh', hJ⟩ := hR (leftToRight τ I) (unop (τ a))
    ((mem_leftToRight τ I a).2 haI) (hne a ha) (unop (τ y))
    ((mem_leftToRight τ I y).2 hy) (unop (τ t)) (hne t ht)
  refine ⟨τ.symm (op h'), hh', leftToRight_injective τ ?_⟩
  rw [← Submodule.span_insert, leftToRight_span, hJ, ← Submodule.span_insert]
  congr 1
  simp [Set.image_insert_eq]

end Left

section Modules

variable {A : Type u} [Ring A] {M : Type v} [AddCommGroup M] [Module A M]

/-- A left `A`-module viewed as a right module through `τ`:
`m * r := τ⁻¹(op r) • m`. This is a local definition, not an instance. -/
abbrev rightOfLeft (τ : A ≃+* Aᵐᵒᵖ) : Module Aᵐᵒᵖ M :=
  Module.compHom M (τ.symm : Aᵐᵒᵖ →+* A)

/-- The right span of `S` in `rightOfLeft τ` is the left span of `S`. -/
theorem span_rightOfLeft (τ : A ≃+* Aᵐᵒᵖ) (S : Set M) :
    ((@Submodule.span Aᵐᵒᵖ M _ _ (rightOfLeft τ) S : Set M)) = Submodule.span A S := by
  let := rightOfLeft (M := M) τ
  apply le_antisymm
  · let N : Submodule Aᵐᵒᵖ M :=
      { carrier := Submodule.span A S
        add_mem' := fun hx hy => Submodule.add_mem _ hx hy
        zero_mem' := Submodule.zero_mem _
        smul_mem' := fun r m hm => Submodule.smul_mem _ (τ.symm r) hm }
    exact (Submodule.span_le (p := N)).2 Submodule.subset_span
  · let N : Submodule A M :=
      { carrier := Submodule.span Aᵐᵒᵖ S
        add_mem' := fun hx hy => Submodule.add_mem _ hx hy
        zero_mem' := Submodule.zero_mem _
        smul_mem' := fun r m hm => by
          have := Submodule.smul_mem _ (τ r) hm
          change τ.symm (τ r) • m ∈ _ at this
          simpa using this }
    exact (Submodule.span_le (p := N)).2 Submodule.subset_span

/-- Prescribed cyclic generator for left modules, from the right statement. -/
theorem prescribedCyclicLeft_of_right (τ : A ≃+* Aᵐᵒᵖ)
    (hR : ∀ (M : Type v) [AddCommGroup M] [Module Aᵐᵒᵖ M] [Module.Finite Aᵐᵒᵖ M],
      (∀ m : M, ∃ d : A, d ≠ 0 ∧ op d • m = 0) →
      ∀ (x : M) (t : A), t ≠ 0 → ∃ h : M, Submodule.span Aᵐᵒᵖ {x + op t • h} = ⊤)
    [Module.Finite A M] (hM : ∀ m : M, ∃ d : A, d ≠ 0 ∧ d • m = 0)
    (x : M) (t : A) (ht : t ≠ 0) :
    ∃ h : M, Submodule.span A {x + t • h} = ⊤ := by
  let := rightOfLeft (M := M) τ
  have hsmul : ∀ (r : Aᵐᵒᵖ) (m : M), r • m = τ.symm r • m := fun _ _ => rfl
  have htop : ∀ S : Set M, Submodule.span Aᵐᵒᵖ S = ⊤ ↔ Submodule.span A S = ⊤ := by
    intro S
    rw [← SetLike.coe_set_eq, ← SetLike.coe_set_eq (q := (⊤ : Submodule A M)),
      span_rightOfLeft]
    rfl
  have : Module.Finite Aᵐᵒᵖ M := by
    obtain ⟨S, hS⟩ := (Module.finite_def.mp ‹Module.Finite A M›)
    exact Module.finite_def.mpr ⟨S, (htop _).2 hS⟩
  have hne : ∀ z : A, z ≠ 0 → unop (τ z) ≠ 0 := fun z hz h0 =>
    hz (τ.injective (by simpa using congrArg op h0))
  obtain ⟨h, hh⟩ := hR M (fun m => by
      obtain ⟨d, hd, hdm⟩ := hM m
      exact ⟨unop (τ d), hne d hd, by simpa [hsmul] using hdm⟩)
    x (unop (τ t)) (hne t ht)
  refine ⟨h, (htop _).1 ?_⟩
  simpa [hsmul] using hh

end Modules

end GeneralizedStafford
