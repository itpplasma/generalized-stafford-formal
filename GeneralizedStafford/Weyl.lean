import GeneralizedStafford.Challenge.Transport
import GeneralizedStafford.Opposite
import AlgebraicAnalysis.Weyl.Simplicity
import AlgebraicAnalysis.Weyl.BernsteinSymbol
import AlgebraicAnalysis.Weyl.Transposition
import AlgebraicAnalysis.Weyl.Domain
import AlgebraicAnalysis.Ore.Noetherian

/-!
# The Weyl algebra `A_n(k)`

The hypotheses (S), (N), (Z) and (H_omega) of the generalized Stafford theorems
hold for the Weyl algebra `A_n(k)` over a field `k` of characteristic zero, by
AlgebraicAnalysis (`Weyl.Simplicity`, `Weyl.BernsteinSymbol`,
`Weyl.Transposition`). This file collects these facts and the consequences
for `A_n(k)`:

* unconditionally, every right ideal and every left ideal of `A_n(k)` is
  two-generated (Corollary C.2), with the left case transferred from the right
  case by the transposition anti-automorphism;
* the Weyl algebra is a domain (AlgebraicAnalysis `Weyl.isDomain`), so every
  nonzero element is regular; this is the input of the regular-element
  consequences below (Theorem A, Theorem A', Corollary C.1 and the
  prescribed-generator form of Corollary C.2).
-/

universe u v

namespace GeneralizedStafford.Weyl

open MulOpposite GeneralizedStaffordChallenge
open AlgebraicAnalysis.Weyl (WeylAlg)

/-! ## Facts from AlgebraicAnalysis -/

/-- `A_n(k)` is simple (S) for a field of characteristic zero. -/
theorem isSimpleRing (k : Type u) [Field k] [CharZero k] (n : ℕ) :
    IsSimpleRing (WeylAlg k n) :=
  AlgebraicAnalysis.Weyl.Simplicity.isSimpleRing_weylAlg k n

/-- `A_n(k)` is right Noetherian (N), from the Bernstein symbol. -/
theorem isNoetherian (k : Type u) [Field k] (n : ℕ) :
    IsNoetherian (WeylAlg k n)ᵐᵒᵖ (WeylAlg k n) :=
  AlgebraicAnalysis.Weyl.BernsteinSymbol.isNoetherian_right k n

/-- `Kdim A_n(k) ≤ ω` (H_omega), from the Bernstein symbol. -/
theorem hOmega (k : Type u) [Field k] (n : ℕ) : HOmega (WeylAlg k n) :=
  hOmega_iff.mpr (AlgebraicAnalysis.Weyl.BernsteinSymbol.devLEOmega_right k n)

/-- The transposition anti-automorphism `A_n(k) ≃+* A_n(k)ᵐᵒᵖ`. -/
def transposeRingEquiv (k : Type u) [Field k] (n : ℕ) :
    WeylAlg k n ≃+* (WeylAlg k n)ᵐᵒᵖ :=
  (AlgebraicAnalysis.Weyl.Transposition.transpositionEquiv k n).toRingEquiv

/-- The centre of `A_n(k)` contains `k`, which is infinite (Z). -/
theorem infinite_center (k : Type u) [Field k] [CharZero k] (n : ℕ) :
    Infinite (Subring.center (WeylAlg k n)) := by
  have := isSimpleRing k n
  have hinj : Function.Injective (algebraMap k (WeylAlg k n)) :=
    (algebraMap k (WeylAlg k n)).injective
  let f : k → Subring.center (WeylAlg k n) := fun c =>
    ⟨algebraMap k (WeylAlg k n) c,
      Subring.mem_center_iff.mpr fun z => (Algebra.commutes c z).symm⟩
  exact Infinite.of_injective f fun a b hab => hinj (congrArg Subtype.val hab)

/-! ## Consequences of the domain property -/

section FromDomain

variable {A : Type u} [Ring A]

/-- A nonzero element of a domain is regular. -/
theorem isRegular_of_ne_zero [IsDomain A] {d : A} (hd : d ≠ 0) : IsRegularElement d :=
  ⟨fun _ hx => (mul_eq_zero.mp hx).resolve_left hd,
   fun _ hx => (mul_eq_zero.mp hx).resolve_right hd⟩

/-- Theorem A for a domain (the Weyl algebra, by AlgebraicAnalysis): the nonzero
anchor `d`, `a` and `B` satisfy `1 = d U + (B + H a) d V`. -/
theorem affine_of_domain [IsSimpleRing A] [IsNoetherian Aᵐᵒᵖ A]
    [Infinite (Subring.center A)] [IsDomain A] (hO : HOmega A)
    (d a B : A) (hd : d ≠ 0) (ha : a ≠ 0) :
    ∃ H U V : A, 1 = d * U + (B + H * a) * d * V :=
  corollaryB_fixedAnchor_proof A hO d a B (isRegular_of_ne_zero hd) ha

/-- Theorem A' for a domain: for a nonzero right ideal `I`, `I + (x + H t) A = A`. -/
theorem fixedIdeal_of_domain [IsSimpleRing A] [IsNoetherian Aᵐᵒᵖ A]
    [Infinite (Subring.center A)] [IsDomain A] (hO : HOmega A)
    (I : Submodule Aᵐᵒᵖ A) (hI : I ≠ ⊥)
    (x t : A) (ht : t ≠ 0) : ∃ H : A, I ⊔ Submodule.span Aᵐᵒᵖ {x + H * t} = ⊤ := by
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  exact corollaryB_fixedIdeal_proof A hO I ⟨s, hs, isRegular_of_ne_zero hs0⟩ x t ht

/-- Corollary C.1 for a domain: a finitely generated module
killed by nonzero scalars has a prescribed cyclic generator. -/
theorem prescribedCyclic_of_domain [IsSimpleRing A] [IsNoetherian Aᵐᵒᵖ A]
    [Infinite (Subring.center A)] [IsDomain A] (hO : HOmega A)
    (M : Type v) [AddCommGroup M] [Module Aᵐᵒᵖ M] [Module.Finite Aᵐᵒᵖ M]
    (hM : ∀ m : M, ∃ d : A, d ≠ 0 ∧ op d • m = 0) (x : M) (t : A) (ht : t ≠ 0) :
    ∃ h : M, Submodule.span Aᵐᵒᵖ {x + op t • h} = ⊤ :=
  corollaryC1_omega_proof A hO M (by
    intro m
    obtain ⟨d, hd, hdm⟩ := hM m
    exact ⟨d, isRegular_of_ne_zero hd, hdm⟩) x t ht

/-- Corollary C.2 for a domain: a nonzero element `a` of a
right ideal `I` is the first generator of a two-generated presentation. -/
theorem prescribedTwoGenerated_of_domain [IsSimpleRing A] [IsNoetherian Aᵐᵒᵖ A]
    [Infinite (Subring.center A)] [IsDomain A] (hO : HOmega A)
    (I : Submodule Aᵐᵒᵖ A) (a : A) (haI : a ∈ I) (ha : a ≠ 0) (y : A) (hy : y ∈ I)
    (t : A) (ht : t ≠ 0) :
    ∃ h ∈ I, I = Submodule.span Aᵐᵒᵖ {a} ⊔ Submodule.span Aᵐᵒᵖ {y + h * t} := by
  refine corollaryC2_prescribed_proof A (corollaryB_dimension_proof A hO).1
    I a haI ?_ y hy t ht
  intro z _
  by_cases hz : z = 0
  · exact ⟨1, isRegular_of_ne_zero one_ne_zero, by simp [hz]⟩
  obtain ⟨r, s, hrs, _⟩ :=
    AlgebraicAnalysis.OreRightIntersection.rightOreCondition_of_isNoetherian ha hz
  have hs : s ≠ 0 := by rintro rfl; simp_all
  refine ⟨s, isRegular_of_ne_zero hs, ?_⟩
  rw [← hrs, Submodule.mem_span_singleton]
  exact ⟨op r, by simp⟩

end FromDomain

/-! ## Two-generated one-sided ideals of `A_n(k)` (unconditional) -/

section TwoGenerated

variable (k : Type u) [Field k] [CharZero k] (n : ℕ)

/-- Every right ideal of `A_n(k)` is two-generated (Corollary C.2). -/
theorem twoGeneratedRight (I : Submodule (WeylAlg k n)ᵐᵒᵖ (WeylAlg k n)) :
    ∃ a b : WeylAlg k n, I = Submodule.span (WeylAlg k n)ᵐᵒᵖ {a, b} := by
  have := isSimpleRing k n
  have := isNoetherian k n
  have := infinite_center k n
  exact corollaryC2_proof (WeylAlg k n) (corollaryB_dimension_proof _ (hOmega k n)).1 I

/-- Every left ideal of `A_n(k)` is two-generated, transferred from the right
case by the transposition anti-automorphism. -/
theorem twoGeneratedLeft (I : Submodule (WeylAlg k n) (WeylAlg k n)) :
    ∃ a b : WeylAlg k n, I = Submodule.span (WeylAlg k n) {a, b} :=
  twoGeneratedLeft_of_right (transposeRingEquiv k n) (twoGeneratedRight k n) I

end TwoGenerated

/-! ## Statements of the Weyl algebra (unconditional)

Each statement is proved for `A_n(k)` of AlgebraicAnalysis, which the challenge
statements use after unfolding the presentation. The domain property is the
AlgebraicAnalysis instance `Weyl.isDomain`, so no hypothesis remains. -/

section Statements

variable (k : Type u) [Field k] [CharZero k] (n : ℕ)

/-- Stafford's Conjecture 3.8 for `A_n(k)`: `1 = d R + F d S` for every nonzero `d`,
from the affine form with `a = 1` and `B = 0`. -/
theorem conjecture38 (d : WeylAlg k n) (hd : d ≠ 0) :
    ∃ F R S : WeylAlg k n, (1 : WeylAlg k n) = d * R + F * d * S := by
  have := isSimpleRing k n
  have := isNoetherian k n
  have := infinite_center k n
  obtain ⟨H, U, V, h⟩ := affine_of_domain (hOmega k n) d 1 0 hd one_ne_zero
  exact ⟨H, U, V, by simpa using h⟩

/-- Theorem A for `A_n(k)`: for `d, a ≠ 0` and any `B` there are `H, U, V`
with `1 = d U + (B + H a) d V`. -/
theorem affineForm (d a B : WeylAlg k n) (hd : d ≠ 0) (ha : a ≠ 0) :
    ∃ H U V : WeylAlg k n, 1 = d * U + (B + H * a) * d * V := by
  have := isSimpleRing k n
  have := isNoetherian k n
  have := infinite_center k n
  exact affine_of_domain (hOmega k n) d a B hd ha

/-- Theorem A' for `A_n(k)`: for a nonzero right ideal `I`, `x` and `t ≠ 0`
there is `H` with `I + (x + H t) A_n(k) = A_n(k)`. -/
theorem fixedIdealForm (I : Submodule (WeylAlg k n)ᵐᵒᵖ (WeylAlg k n)) (hI : I ≠ ⊥)
    (x t : WeylAlg k n) (ht : t ≠ 0) :
    ∃ H : WeylAlg k n, I ⊔ Submodule.span (WeylAlg k n)ᵐᵒᵖ {x + H * t} = ⊤ := by
  have := isSimpleRing k n
  have := isNoetherian k n
  have := infinite_center k n
  exact fixedIdeal_of_domain (hOmega k n) I hI x t ht

/-- Corollary C.1 for right modules over `A_n(k)`: a finitely generated torsion
right module has, for every `x` and `t ≠ 0`, an `h` with `M = (x + h t)A_n(k)`. -/
theorem prescribedCyclicRight (M : Type v) [AddCommGroup M]
    [Module (WeylAlg k n)ᵐᵒᵖ M] [Module.Finite (WeylAlg k n)ᵐᵒᵖ M]
    (hM : ∀ m : M, ∃ d : WeylAlg k n, d ≠ 0 ∧ op d • m = 0)
    (x : M) (t : WeylAlg k n) (ht : t ≠ 0) :
    ∃ h : M, Submodule.span (WeylAlg k n)ᵐᵒᵖ {x + op t • h} = ⊤ := by
  have := isSimpleRing k n
  have := isNoetherian k n
  have := infinite_center k n
  exact prescribedCyclic_of_domain (hOmega k n) M hM x t ht

/-- Corollary C.1 for left modules over `A_n(k)`, transferred from the right case
by the transposition anti-automorphism. -/
theorem prescribedCyclicLeft (M : Type v) [AddCommGroup M]
    [Module (WeylAlg k n) M] [Module.Finite (WeylAlg k n) M]
    (hM : ∀ m : M, ∃ d : WeylAlg k n, d ≠ 0 ∧ d • m = 0)
    (x : M) (t : WeylAlg k n) (ht : t ≠ 0) :
    ∃ h : M, Submodule.span (WeylAlg k n) {x + t • h} = ⊤ := by
  refine prescribedCyclicLeft_of_right (M := M) (transposeRingEquiv k n) ?_ hM x t ht
  intro M _ _ _ hM x t ht
  exact prescribedCyclicRight k n M hM x t ht

/-- Torsion cyclicity for right modules: a finitely generated torsion right
`A_n(k)`-module is cyclic (the case `x = 0`, `t = 1` of the prescribed form). -/
theorem torsionCyclicRight (M : Type v) [AddCommGroup M]
    [Module (WeylAlg k n)ᵐᵒᵖ M] [Module.Finite (WeylAlg k n)ᵐᵒᵖ M]
    (hM : ∀ m : M, ∃ d : WeylAlg k n, d ≠ 0 ∧ op d • m = 0) :
    ∃ z : M, Submodule.span (WeylAlg k n)ᵐᵒᵖ ({z} : Set M) = ⊤ := by
  have := isSimpleRing k n
  obtain ⟨h, hh⟩ := prescribedCyclicRight k n M hM 0 1 one_ne_zero
  exact ⟨h, by simpa using hh⟩

/-- Torsion cyclicity for left modules over `A_n(k)`. -/
theorem torsionCyclicLeft (M : Type v) [AddCommGroup M]
    [Module (WeylAlg k n) M] [Module.Finite (WeylAlg k n) M]
    (hM : ∀ m : M, ∃ d : WeylAlg k n, d ≠ 0 ∧ d • m = 0) :
    ∃ z : M, Submodule.span (WeylAlg k n) ({z} : Set M) = ⊤ := by
  have := isSimpleRing k n
  obtain ⟨h, hh⟩ := prescribedCyclicLeft k n M hM 0 1 one_ne_zero
  exact ⟨h, by simpa using hh⟩

/-- Corollary C.2, prescribed first generator, for right ideals of `A_n(k)`. -/
theorem prescribedTwoGeneratedRight (I : Submodule (WeylAlg k n)ᵐᵒᵖ (WeylAlg k n))
    (a : WeylAlg k n) (haI : a ∈ I) (ha : a ≠ 0) (y : WeylAlg k n) (hy : y ∈ I)
    (t : WeylAlg k n) (ht : t ≠ 0) :
    ∃ h ∈ I, I = Submodule.span (WeylAlg k n)ᵐᵒᵖ {a} ⊔
      Submodule.span (WeylAlg k n)ᵐᵒᵖ {y + h * t} := by
  have := isSimpleRing k n
  have := isNoetherian k n
  have := infinite_center k n
  exact prescribedTwoGenerated_of_domain (hOmega k n) I a haI ha y hy t ht

/-- Corollary C.2, prescribed first generator, for left ideals of `A_n(k)`. -/
theorem prescribedTwoGeneratedLeft (I : Submodule (WeylAlg k n) (WeylAlg k n))
    (a : WeylAlg k n) (haI : a ∈ I) (ha : a ≠ 0) (y : WeylAlg k n) (hy : y ∈ I)
    (t : WeylAlg k n) (ht : t ≠ 0) :
    ∃ h ∈ I, I = Submodule.span (WeylAlg k n) {a} ⊔
      Submodule.span (WeylAlg k n) {y + t * h} := by
  refine prescribedTwoGeneratedLeft_of_right (transposeRingEquiv k n) ?_ I a haI ha y hy t ht
  intro J a haJ ha y hy t ht
  exact prescribedTwoGeneratedRight k n J a haJ ha y hy t ht

end Statements

end GeneralizedStafford.Weyl
