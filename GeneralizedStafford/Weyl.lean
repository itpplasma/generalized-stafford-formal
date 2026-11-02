import GeneralizedStafford.Challenge.Transport
import GeneralizedStafford.Opposite
import AlgebraicAnalysis.Weyl.Simplicity
import AlgebraicAnalysis.Weyl.BernsteinSymbol
import AlgebraicAnalysis.Weyl.Transposition
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
* the nonzero-divisor property of `A_n(k)`, `NoZeroDivisorsWeyl`, is the one
  Weyl fact that AlgebraicAnalysis does not yet provide. It is a hypothesis of
  the other consequences (Theorem A, Theorem A', Corollary C.1 and the
  prescribed-generator form of Corollary C.2), each of which needs that every
  nonzero element is regular.
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

/-! ## The one missing Weyl fact -/

/-- `A_n(k)` has no zero divisors: a product of nonzero elements is nonzero.
This is the statement that `A_n(k)` is a domain. AlgebraicAnalysis does not yet
prove it, so every consequence that needs regular elements takes it as an
explicit hypothesis. -/
def NoZeroDivisorsWeyl (k : Type u) [Field k] (n : ℕ) : Prop :=
  ∀ a b : WeylAlg k n, a ≠ 0 → b ≠ 0 → a * b ≠ 0

/-! ## Generic consequences of a nonzero-divisor property -/

section FromDomain

variable {A : Type u} [Ring A]

/-- A nonzero element of a ring without zero divisors is regular. -/
theorem isRegular_of_mul_ne_zero (hD : ∀ a b : A, a ≠ 0 → b ≠ 0 → a * b ≠ 0)
    {d : A} (hd : d ≠ 0) : IsRegularElement d :=
  ⟨fun x hx => by_contra fun hx0 => hD d x hd hx0 hx,
   fun x hx => by_contra fun hx0 => hD x d hx0 hd hx⟩

/-- Theorem A for a ring without zero divisors: the nonzero anchor `d`, `a` and
`B` satisfy `1 = d U + (B + H a) d V`. -/
theorem affine_of_domain [IsSimpleRing A] [IsNoetherian Aᵐᵒᵖ A]
    [Infinite (Subring.center A)] (hO : HOmega A)
    (hD : ∀ a b : A, a ≠ 0 → b ≠ 0 → a * b ≠ 0) (d a B : A) (hd : d ≠ 0) (ha : a ≠ 0) :
    ∃ H U V : A, 1 = d * U + (B + H * a) * d * V :=
  corollaryB_fixedAnchor_proof A hO d a B (isRegular_of_mul_ne_zero hD hd) ha

/-- Theorem A' for a ring without zero divisors: for a nonzero right ideal `I`,
`I + (x + H t) A = A`. -/
theorem fixedIdeal_of_domain [IsSimpleRing A] [IsNoetherian Aᵐᵒᵖ A]
    [Infinite (Subring.center A)] (hO : HOmega A)
    (hD : ∀ a b : A, a ≠ 0 → b ≠ 0 → a * b ≠ 0) (I : Submodule Aᵐᵒᵖ A) (hI : I ≠ ⊥)
    (x t : A) (ht : t ≠ 0) : ∃ H : A, I ⊔ Submodule.span Aᵐᵒᵖ {x + H * t} = ⊤ := by
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  exact corollaryB_fixedIdeal_proof A hO I ⟨s, hs, isRegular_of_mul_ne_zero hD hs0⟩ x t ht

/-- Corollary C.1 for a ring without zero divisors: a finitely generated module
killed by nonzero scalars has a prescribed cyclic generator. -/
theorem prescribedCyclic_of_domain [IsSimpleRing A] [IsNoetherian Aᵐᵒᵖ A]
    [Infinite (Subring.center A)] (hO : HOmega A)
    (hD : ∀ a b : A, a ≠ 0 → b ≠ 0 → a * b ≠ 0)
    (M : Type v) [AddCommGroup M] [Module Aᵐᵒᵖ M] [Module.Finite Aᵐᵒᵖ M]
    (hM : ∀ m : M, ∃ d : A, d ≠ 0 ∧ op d • m = 0) (x : M) (t : A) (ht : t ≠ 0) :
    ∃ h : M, Submodule.span Aᵐᵒᵖ {x + op t • h} = ⊤ :=
  corollaryC1_omega_proof A hO M (by
    intro m
    obtain ⟨d, hd, hdm⟩ := hM m
    exact ⟨d, isRegular_of_mul_ne_zero hD hd, hdm⟩) x t ht

/-- Corollary C.2 for a ring without zero divisors: a nonzero element `a` of a
right ideal `I` is the first generator of a two-generated presentation. -/
theorem prescribedTwoGenerated_of_domain [IsSimpleRing A] [IsNoetherian Aᵐᵒᵖ A]
    [Infinite (Subring.center A)] (hO : HOmega A)
    (hD : ∀ a b : A, a ≠ 0 → b ≠ 0 → a * b ≠ 0)
    (I : Submodule Aᵐᵒᵖ A) (a : A) (haI : a ∈ I) (ha : a ≠ 0) (y : A) (hy : y ∈ I)
    (t : A) (ht : t ≠ 0) :
    ∃ h ∈ I, I = Submodule.span Aᵐᵒᵖ {a} ⊔ Submodule.span Aᵐᵒᵖ {y + h * t} := by
  have : IsDomain A := by
    have : NoZeroDivisors A := ⟨fun {a b} hab => by
      by_contra hne
      push Not at hne
      exact hD a b hne.1 hne.2 hab⟩
    exact NoZeroDivisors.to_isDomain A
  refine corollaryC2_prescribed_proof A (corollaryB_dimension_proof A hO).1
    I a haI ?_ y hy t ht
  intro z _
  by_cases hz : z = 0
  · exact ⟨1, isRegular_of_mul_ne_zero hD one_ne_zero, by simp [hz]⟩
  obtain ⟨r, s, hrs, _⟩ :=
    AlgebraicAnalysis.OreRightIntersection.rightOreCondition_of_isNoetherian ha hz
  have hs : s ≠ 0 := by rintro rfl; simp_all
  refine ⟨s, isRegular_of_mul_ne_zero hD hs, ?_⟩
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

end GeneralizedStafford.Weyl
