module

public import GeneralizedStafford.Challenge.FilteredTransport
public import GeneralizedStafford.Weyl
public import AlgebraicAnalysis.DifferentialOperators.SmoothOperators
public import AlgebraicAnalysis.Filtration.Opposite

@[expose] public section

/-!
# Rings of differential operators `D_k(A)`

Let `k` be a field of characteristic zero and `A` a smooth domain of finite type over `k`.
The ring `D = D_k(A)` of finite-order `k`-linear differential operators on `A` satisfies (S),
(N), (Z) and (H_omega) on both sides, by AlgebraicAnalysis (`SmoothOperators`): `D` is simple
and a domain, it is right and left Noetherian, its right and left deviations are at most
`2r` for `r` generators of `A`, and its centre is infinite. The conclusions of Theorem A,
Theorem A', Corollary B and Corollaries C.1 and C.2 then follow for `D` and for `Dᵐᵒᵖ` from
the abstract theorems of `GeneralizedStafford.Challenge.FilteredTransport`.

This file proves:

* `GeneralizedStafford.DiffOp.conclusions_right`, `conclusions_left`: all conclusions for `D`
  (right ideals and modules) and for `Dᵐᵒᵖ` (left ideals and modules).
* `affineForm_right`, `affineForm_left`: Theorem A, right form `1 = d U + (B + H a) d V` and
  left form `1 = U d + V d (B + a H)`, for nonzero `d` and `a`, as statements about elements of
  `Module.End k A` lying in `D_k(A)`.
* `globalStafford`: `1 = d R + F d S` for nonzero `d`.
* `twoGenerated_left_ideal`, `prescribedCyclicLeft`: the left-ideal and left-module forms, with
  the same proofs transported through the opposite ring.
-/

universe u v

set_option linter.unusedSectionVars false

open MulOpposite GeneralizedStaffordChallenge
open AlgebraicAnalysis.DifferentialOperators.SmoothOperators (DiffOp)

namespace GeneralizedStafford.DiffOp

/-! ## Hypotheses (S), (N), (Z) and (H_omega) for `D_k(A)` -/

section Hypotheses

variable (k : Type u) (A : Type u) [Field k] [CharZero k] [CommRing A] [IsDomain A]
  [Algebra k A] [Algebra.Smooth k A]

/-- `D_k(A)` is a simple ring (S). -/
theorem isSimpleRing : IsSimpleRing (DiffOp k A) :=
  AlgebraicAnalysis.DifferentialOperators.SmoothOperators.isSimpleRing k A

/-- `D_k(A)` is a domain. -/
theorem isDomain : IsDomain (DiffOp k A) :=
  AlgebraicAnalysis.DifferentialOperators.SmoothOperators.isDomain k A

/-- `D_k(A)` is right Noetherian (N): `IsNoetherian D_ᵐᵒᵖ D`. -/
theorem noetherianRight : IsNoetherian (DiffOp k A)ᵐᵒᵖ (DiffOp k A) :=
  AlgebraicAnalysis.DifferentialOperators.SmoothOperators.isNoetherian_right k A

/-- `D_k(A)ᵐᵒᵖ` is right Noetherian, that is `D_k(A)` is left Noetherian (N). -/
theorem noetherianLeft : IsNoetherian (DiffOp k A)ᵐᵒᵖᵐᵒᵖ (DiffOp k A)ᵐᵒᵖ :=
  (AlgebraicAnalysis.isNoetherian_right_op_iff (DiffOp k A)).mpr
    (AlgebraicAnalysis.DifferentialOperators.SmoothOperators.isNoetherianRing k A)

/-- `D_k(A)` has infinite centre (Z). -/
theorem infiniteCenterRight : Infinite (Subring.center (DiffOp k A)) :=
  AlgebraicAnalysis.DifferentialOperators.SmoothOperators.infinite_center k A

/-- `D_k(A)ᵐᵒᵖ` has infinite centre (Z). -/
theorem infiniteCenterLeft : Infinite (Subring.center (DiffOp k A)ᵐᵒᵖ) := by
  have := isDomain k A
  have : Infinite k := CharZero.infinite k
  exact AlgebraicAnalysis.infinite_subring_center k (DiffOp k A)ᵐᵒᵖ

/-- (H_omega) for the right regular module `D_k(A)`. -/
theorem homegaRight : HOmega (DiffOp k A) :=
  hOmega_iff.mpr (AlgebraicAnalysis.DifferentialOperators.SmoothOperators.devLEOmega_right k A)

/-- (H_omega) for `D_k(A)ᵐᵒᵖ`, that is the left ideals of `D_k(A)` have deviation at most
`ω`. The generating set of `A` gives the finite deviation `2r`, transported to the
opposite side. -/
theorem homegaLeft : HOmega (DiffOp k A)ᵐᵒᵖ := by
  obtain ⟨r, x, hx, -⟩ :=
    AlgebraicAnalysis.DifferentialOperators.SmoothOperators.exists_isProjectiveFrame' k A
  exact hOmega_iff.mpr
    ((AlgebraicAnalysis.devLE_right_op_iff (DiffOp k A) (r + r)).mpr
      (AlgebraicAnalysis.DifferentialOperators.SmoothOperators.devLE_left hx)).omega

end Hypotheses

/-! ## Conclusions for `D_k(A)` and `D_k(A)ᵐᵒᵖ` -/

section Conclusions

variable (k : Type u) (A : Type u) [Field k] [CharZero k] [CommRing A] [IsDomain A]
  [Algebra k A] [Algebra.Smooth k A]

/-- All conclusions of Theorem A', Theorem A, Corollary B and Corollaries C.1 and C.2 for a
simple domain-like ring `R` with (N), (Z) and (H_omega). -/
theorem conclusions_of (R : Type u) [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    [Infinite (Subring.center R)] (homega : HOmega R) :
    FixedAnchorProperty R ∧ FixedIdealProperty R ∧
      PrescribedCyclicProperty.{u, v} R ∧ StablyCyclicProperty.{u, v} R ∧
      TwoGeneratedProperty R :=
  ⟨fixedAnchorProperty_of_omega homega, fixedIdealProperty_of_omega homega,
    prescribedCyclicProperty_of_omega homega,
    stablyCyclic_of_omega homega, twoGeneratedProperty_of_omega homega⟩

/-- Theorem A', Theorem A, Corollary B and Corollaries C.1 and C.2 for `D_k(A)`, right ideals
and right modules. -/
theorem conclusions_right :
    FixedAnchorProperty (DiffOp k A) ∧ FixedIdealProperty (DiffOp k A) ∧
      PrescribedCyclicProperty.{u, v} (DiffOp k A) ∧
      StablyCyclicProperty.{u, v} (DiffOp k A) ∧ TwoGeneratedProperty (DiffOp k A) := by
  have hS : IsSimpleRing (DiffOp k A) := isSimpleRing k A
  have hN : IsNoetherian (DiffOp k A)ᵐᵒᵖ (DiffOp k A) := noetherianRight k A
  have hZ : Infinite (Subring.center (DiffOp k A)) := infiniteCenterRight k A
  exact conclusions_of (DiffOp k A) (homegaRight k A)

/-- The same conclusions for `D_k(A)ᵐᵒᵖ`, that is for the left ideals and left modules of
`D_k(A)`. -/
theorem conclusions_left :
    FixedAnchorProperty (DiffOp k A)ᵐᵒᵖ ∧ FixedIdealProperty (DiffOp k A)ᵐᵒᵖ ∧
      PrescribedCyclicProperty.{u, v} (DiffOp k A)ᵐᵒᵖ ∧
      StablyCyclicProperty.{u, v} (DiffOp k A)ᵐᵒᵖ ∧ TwoGeneratedProperty (DiffOp k A)ᵐᵒᵖ := by
  have hS : IsSimpleRing (DiffOp k A) := isSimpleRing k A
  have hN : IsNoetherian (DiffOp k A)ᵐᵒᵖᵐᵒᵖ (DiffOp k A)ᵐᵒᵖ := noetherianLeft k A
  have hZ : Infinite (Subring.center (DiffOp k A)ᵐᵒᵖ) := infiniteCenterLeft k A
  have hS' : IsSimpleRing (DiffOp k A)ᵐᵒᵖ := inferInstance
  exact conclusions_of (DiffOp k A)ᵐᵒᵖ (homegaLeft k A)

end Conclusions

/-! ## Element forms: Theorem A and the Global Stafford identity -/

section Elements

variable (k : Type u) (A : Type u) [Field k] [CharZero k] [CommRing A] [IsDomain A]
  [Algebra k A] [Algebra.Smooth k A]

/-- `D_k(A)` as a subalgebra of `Module.End k A`: the operators of finite order. -/
abbrev Dsub (k A : Type u) [Field k] [CommRing A] [Algebra k A] :
    Subalgebra k (Module.End k A) :=
  AlgebraicAnalysis.DifferentialOperators.algebra (k := k) (R := A)

/-- **Theorem A, right form.** For differential operators `d, a, B` on `A` with `d ≠ 0` and
`a ≠ 0` there are differential operators `H, U, V` with `1 = d U + (B + H a) d V`. -/
theorem affineForm_right (d a B : Module.End k A) (hd : d ∈ Dsub k A) (hd0 : d ≠ 0)
    (ha : a ∈ Dsub k A) (ha0 : a ≠ 0) (hB : B ∈ Dsub k A) :
    ∃ H U V : Module.End k A, H ∈ Dsub k A ∧ U ∈ Dsub k A ∧ V ∈ Dsub k A ∧
      (1 : Module.End k A) = d * U + (B + H * a) * d * V := by
  have := isDomain k A
  have hS : IsSimpleRing (DiffOp k A) := isSimpleRing k A
  have hN : IsNoetherian (DiffOp k A)ᵐᵒᵖ (DiffOp k A) := noetherianRight k A
  have hZ : Infinite (Subring.center (DiffOp k A)) := infiniteCenterRight k A
  have hd' : (⟨d, hd⟩ : DiffOp k A) ≠ 0 := fun h => hd0 (by simpa using congrArg Subtype.val h)
  have hreg : IsRegularElement (⟨d, hd⟩ : DiffOp k A) := Weyl.isRegular_of_ne_zero hd'
  have ha' : (⟨a, ha⟩ : DiffOp k A) ≠ 0 := fun h => ha0 (by simpa using congrArg Subtype.val h)
  obtain ⟨H, U, V, h⟩ :=
    (fixedAnchorProperty_of_omega (R := DiffOp k A) (homegaRight k A)
      : FixedAnchorProperty (DiffOp k A)) ⟨d, hd⟩ ⟨a, ha⟩ ⟨B, hB⟩ hreg ha'
  refine ⟨H, U, V, H.2, U.2, V.2, ?_⟩
  have := congrArg Subtype.val h
  simpa using this

/-- **Theorem A, left form.** For differential operators `d, a, B` on `A` with `d ≠ 0` and
`a ≠ 0` there are differential operators `H, U, V` with `1 = U d + V d (B + a H)`. -/
theorem affineForm_left (d a B : Module.End k A) (hd : d ∈ Dsub k A) (hd0 : d ≠ 0)
    (ha : a ∈ Dsub k A) (ha0 : a ≠ 0) (hB : B ∈ Dsub k A) :
    ∃ H U V : Module.End k A, H ∈ Dsub k A ∧ U ∈ Dsub k A ∧ V ∈ Dsub k A ∧
      (1 : Module.End k A) = U * d + V * d * (B + a * H) := by
  have := isDomain k A
  have hS : IsSimpleRing (DiffOp k A) := isSimpleRing k A
  have hN : IsNoetherian (DiffOp k A)ᵐᵒᵖᵐᵒᵖ (DiffOp k A)ᵐᵒᵖ := noetherianLeft k A
  have hZ : Infinite (Subring.center (DiffOp k A)ᵐᵒᵖ) := infiniteCenterLeft k A
  have hS' : IsSimpleRing (DiffOp k A)ᵐᵒᵖ := inferInstance
  have hd' : (⟨d, hd⟩ : DiffOp k A) ≠ 0 := fun h => hd0 (by simpa using congrArg Subtype.val h)
  have ha' : (⟨a, ha⟩ : DiffOp k A) ≠ 0 := fun h => ha0 (by simpa using congrArg Subtype.val h)
  have hreg : IsRegularElement (op (⟨d, hd⟩ : DiffOp k A)) :=
    Weyl.isRegular_of_ne_zero (fun h => hd' (by simpa using h))
  have ha'' : op (⟨a, ha⟩ : DiffOp k A) ≠ 0 := fun h => ha' (by simpa using h)
  obtain ⟨H, U, V, h⟩ :=
    (fixedAnchorProperty_of_omega (R := (DiffOp k A)ᵐᵒᵖ) (homegaLeft k A)
      : FixedAnchorProperty (DiffOp k A)ᵐᵒᵖ)
      (op ⟨d, hd⟩) (op ⟨a, ha⟩) (op ⟨B, hB⟩) hreg ha''
  have h' := congrArg (fun z : (DiffOp k A)ᵐᵒᵖ => ((unop z : DiffOp k A) : Module.End k A)) h
  refine ⟨((unop H : DiffOp k A) : Module.End k A), ((unop U : DiffOp k A) : Module.End k A),
    ((unop V : DiffOp k A) : Module.End k A), (unop H).2, (unop U).2, (unop V).2, ?_⟩
  simpa [mul_assoc] using h'

/-- **Global Stafford identity.** For a nonzero differential operator `d` on `A` there are
differential operators `F, R, S` with `1 = d R + F d S`. This is Theorem A with `a = 1`
and `B = 0`. -/
theorem globalStafford (d : Module.End k A) (hd : d ∈ Dsub k A) (hd0 : d ≠ 0) :
    ∃ F R S : Module.End k A, F ∈ Dsub k A ∧ R ∈ Dsub k A ∧ S ∈ Dsub k A ∧
      (1 : Module.End k A) = d * R + F * d * S := by
  obtain ⟨H, U, V, hH, hU, hV, h⟩ :=
    affineForm_right k A d 1 0 hd hd0 (Dsub k A).one_mem one_ne_zero (Dsub k A).zero_mem
  exact ⟨H, U, V, hH, hU, hV, by simpa using h⟩

end Elements

/-! ## Left ideals and left modules through the opposite ring -/

section Opposite

variable {R : Type u} [Ring R]

/-- The ring homomorphism `Rᵐᵒᵖᵐᵒᵖ → R`, `op (op r) ↦ r`. -/
def opOpHom (R : Type u) [Ring R] : Rᵐᵒᵖᵐᵒᵖ →+* R where
  toFun x := unop (unop x)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A left `R`-module as a module over `Rᵐᵒᵖᵐᵒᵖ`, with `op (op r) • m = r • m`. A left module
is a right module over the opposite ring. This is a local construction, not an instance. -/
abbrev leftAsRight (M : Type v) [AddCommGroup M] [Module R M] : Module Rᵐᵒᵖᵐᵒᵖ M :=
  Module.compHom M (opOpHom R)

/-- The span over `Rᵐᵒᵖᵐᵒᵖ` of a set is its span over `R`. -/
theorem span_leftAsRight (M : Type v) [AddCommGroup M] [Module R M] (S : Set M) :
    (@Submodule.span Rᵐᵒᵖᵐᵒᵖ M _ _ (leftAsRight M) S : Set M) = Submodule.span R S := by
  letI := leftAsRight (R := R) M
  apply le_antisymm
  · let N : Submodule Rᵐᵒᵖᵐᵒᵖ M :=
      { carrier := (Submodule.span R S : Set M)
        add_mem' := fun hx hy => Submodule.add_mem _ hx hy
        zero_mem' := Submodule.zero_mem _
        smul_mem' := fun c _ hm => Submodule.smul_mem _ (opOpHom R c) hm }
    have hle : Submodule.span Rᵐᵒᵖᵐᵒᵖ S ≤ N :=
      Submodule.span_le.mpr fun s hs => Submodule.subset_span hs
    exact fun m hm => hle hm
  · let N : Submodule R M :=
      { carrier := (Submodule.span Rᵐᵒᵖᵐᵒᵖ S : Set M)
        add_mem' := fun hx hy => Submodule.add_mem _ hx hy
        zero_mem' := Submodule.zero_mem _
        smul_mem' := fun r _ hm => Submodule.smul_mem _ (op (op r)) hm }
    have hle : Submodule.span R S ≤ N :=
      Submodule.span_le.mpr fun s hs => Submodule.subset_span hs
    exact fun m hm => hle hm

/-- Left ideals of `R` are two-generated, from the two-generation of right ideals of `Rᵐᵒᵖ`:
a left ideal `I` is the right ideal `{op x | x ∈ I}` of `Rᵐᵒᵖ`. -/
theorem twoGenerated_left_of_op
    (hR : ∀ J : Submodule Rᵐᵒᵖᵐᵒᵖ Rᵐᵒᵖ, ∃ a b : Rᵐᵒᵖ, J = Submodule.span Rᵐᵒᵖᵐᵒᵖ {a, b})
    (I : Submodule R R) : ∃ a b : R, I = Submodule.span R {a, b} := by
  obtain ⟨a, b, hab⟩ := hR ((AlgebraicAnalysis.rightIdealOpEquiv R).symm I)
  refine ⟨unop a, unop b, ?_⟩
  ext x
  have hx : x ∈ I ↔ op x ∈ (AlgebraicAnalysis.rightIdealOpEquiv R).symm I := Iff.rfl
  rw [hx, hab, Submodule.mem_span_pair, Submodule.mem_span_pair]
  constructor
  · rintro ⟨c, d, hcd⟩
    refine ⟨unop (unop c), unop (unop d), ?_⟩
    have h1 := congrArg unop hcd
    simpa [MulOpposite.smul_eq_mul_unop, smul_eq_mul] using h1
  · rintro ⟨c, d, hcd⟩
    refine ⟨op (op c), op (op d), ?_⟩
    apply unop_injective
    simpa [MulOpposite.smul_eq_mul_unop, smul_eq_mul] using hcd

/-- Prescribed cyclic generator for left modules over `R`, from the right statement for `Rᵐᵒᵖ`:
a finitely generated left module killed by nonzero elements `d` (each `d • m = 0`) satisfies
`M = R (x + t h)` for every `x` and nonzero `t`. -/
theorem prescribedCyclicLeft_of_property [IsDomain R]
    (hP : PrescribedCyclicProperty.{u, v} Rᵐᵒᵖ)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : ∀ m : M, ∃ d : R, d ≠ 0 ∧ d • m = 0) (x : M) (t : R) (ht : t ≠ 0) :
    ∃ h : M, Submodule.span R {x + t • h} = ⊤ := by
  letI := leftAsRight (R := R) M
  have hfin : Module.Finite Rᵐᵒᵖᵐᵒᵖ M := by
    obtain ⟨S, hS⟩ := Module.finite_def.mp ‹Module.Finite R M›
    refine Module.finite_def.mpr ⟨S, ?_⟩
    have key := span_leftAsRight (R := R) M (S : Set M)
    rw [hS] at key
    apply Submodule.eq_top_iff'.mpr
    intro m
    have hm : m ∈ (Submodule.span Rᵐᵒᵖᵐᵒᵖ (S : Set M) : Set M) := by
      rw [show (Submodule.span Rᵐᵒᵖᵐᵒᵖ (S : Set M) : Set M) = ↑(⊤ : Submodule R M) from key]
      exact Submodule.mem_top
    exact hm
  have hG : IsGoldieTorsion Rᵐᵒᵖ M := fun m => by
    obtain ⟨d, hd, hdm⟩ := hM m
    exact ⟨op d, Weyl.isRegular_of_ne_zero (fun h => hd (by simpa using h)), hdm⟩
  obtain ⟨h, hh⟩ := hP M hG x (op t) (fun h => ht (by simpa using h))
  refine ⟨h, ?_⟩
  apply Submodule.eq_top_iff'.mpr
  intro m
  have key := span_leftAsRight (R := R) M ({x + t • h} : Set M)
  have hh' : Submodule.span Rᵐᵒᵖᵐᵒᵖ ({x + t • h} : Set M) = ⊤ := hh
  have hm : m ∈ (Submodule.span Rᵐᵒᵖᵐᵒᵖ ({x + t • h} : Set M) : Set M) := by
    rw [hh']
    exact Submodule.mem_top
  rw [key] at hm
  exact hm

end Opposite

/-! ## Two-generated ideals and prescribed cyclic modules of `D_k(A)` -/

section Statements

variable (k : Type u) (A : Type u) [Field k] [CharZero k] [CommRing A] [IsDomain A]
  [Algebra k A] [Algebra.Smooth k A]

/-- Every right ideal of `D_k(A)` is two-generated (C.2). -/
theorem twoGeneratedRight (I : Submodule (DiffOp k A)ᵐᵒᵖ (DiffOp k A)) :
    ∃ a b : DiffOp k A, I = Submodule.span (DiffOp k A)ᵐᵒᵖ {a, b} :=
  (conclusions_right.{u, u} k A).2.2.2.2.2 I

/-- Every left ideal of `D_k(A)` is two-generated (C.2), from the right statement for
`D_k(A)ᵐᵒᵖ`. -/
theorem twoGeneratedLeft (I : Submodule (DiffOp k A) (DiffOp k A)) :
    ∃ a b : DiffOp k A, I = Submodule.span (DiffOp k A) {a, b} :=
  twoGenerated_left_of_op (fun J => (conclusions_left.{u, u} k A).2.2.2.2.2 J) I

/-- Corollary C.1 for finitely generated right `D_k(A)`-modules killed by nonzero operators. -/
theorem prescribedCyclicRight (M : Type v) [AddCommGroup M] [Module (DiffOp k A)ᵐᵒᵖ M]
    [Module.Finite (DiffOp k A)ᵐᵒᵖ M]
    (hM : ∀ m : M, ∃ s : DiffOp k A, s ≠ 0 ∧ op s • m = 0)
    (x : M) (t : DiffOp k A) (ht : t ≠ 0) :
    ∃ h : M, Submodule.span (DiffOp k A)ᵐᵒᵖ {x + op t • h} = ⊤ := by
  have := isDomain k A
  have hG : IsGoldieTorsion (DiffOp k A) M := fun m => by
    obtain ⟨s, hs, hsm⟩ := hM m
    exact ⟨s, Weyl.isRegular_of_ne_zero hs, hsm⟩
  exact (conclusions_right.{u, v} k A).2.2.1 M hG x t ht

/-- Corollary C.1 for finitely generated left `D_k(A)`-modules killed by nonzero operators. -/
theorem prescribedCyclicLeft (M : Type v) [AddCommGroup M] [Module (DiffOp k A) M]
    [Module.Finite (DiffOp k A) M]
    (hM : ∀ m : M, ∃ s : DiffOp k A, s ≠ 0 ∧ s • m = 0)
    (x : M) (t : DiffOp k A) (ht : t ≠ 0) :
    ∃ h : M, Submodule.span (DiffOp k A) {x + t • h} = ⊤ := by
  have := isDomain k A
  exact prescribedCyclicLeft_of_property (conclusions_left.{u, v} k A).2.2.1 M
    (fun m => by
      obtain ⟨s, hs, hsm⟩ := hM m
      exact ⟨s, hs, hsm⟩) x t ht

end Statements

end GeneralizedStafford.DiffOp
