module

public import GeneralizedStafford.CorollaryB
public import GeneralizedStafford.Modules
public import AlgebraicAnalysis.Filtration.Opposite
public import AlgebraicAnalysis.Filtration.SymbolNoetherian
public import AlgebraicAnalysis.RingTheory.InfiniteCenter

@[expose] public section

/-!
# Filtered rings with commutative Noetherian associated graded ring

Proposition `prop:filtered` of the manuscript. Let `k` be an infinite field and
`R` a simple `k`-algebra with an exhaustive filtration `φ` and a symbol
`S : φ.GradedSymbol 𝒜` identifying `gr R` with a commutative graded algebra
`G = ⨁ 𝒜ₙ` of Krull dimension at most `m`, with `G` Noetherian. Then `R` and
`Rᵐᵒᵖ` satisfy (S), (N), (Z) and (H_ω), and hence Theorem A, Theorem A',
Corollary B, Corollary C.1 and C.2 hold for `R` and for `Rᵐᵒᵖ`, that is
on both sides.

* `GeneralizedStafford.right_side`: right Noetherianity and right deviation
  bounds from the symbol (AlgebraicAnalysis' `GradedSymbol` lemmas).
* `GeneralizedStafford.filtered_hypotheses`: (N), (Z) and `Kdim ≤ m` on both
  sides, using the opposite filtration and the opposite symbol for `Rᵐᵒᵖ`.
* `GeneralizedStafford.filtered_theoremA` and the following theorems: the
  conclusions for each side, reusing the abstract theorems of
  `TheoremA`, `CorollaryB` and `Modules`.
-/

universe u v

namespace GeneralizedStafford

open MulOpposite nonZeroDivisors AlgebraicAnalysis AlgebraicAnalysis.Goldie
open AlgebraicAnalysis.DenominatorTorsion

section Hypotheses

variable {k : Type*} [Field k] {R : Type u} [Ring R] [Algebra k R]
variable {G : Type*} [CommRing G] [Algebra k G] {𝒜 : ℕ → Submodule k G}

/-- A Krull dimension bounded by a natural number is not `⊤`. -/
theorem ringKrullDim_ne_top_of_le {x : WithBot ℕ∞} {m : ℕ} (hx : x ≤ m) : x ≠ ⊤ :=
  ne_top_of_le_ne_top (fun h => by cases h) hx

/-- **Right side of a symbol.** Let `S` identify `gr R` with a commutative
Noetherian graded algebra `G` of Krull dimension at most `m`. Then `R` is right
Noetherian, and the right ideals of `R` have deviation at most `m` and at most
`ω`. -/
theorem right_side [IsNoetherianRing G] [GradedAlgebra 𝒜] {φ : RingFiltration k R}
    (S : φ.GradedSymbol 𝒜) {m : ℕ} (hm : ringKrullDim G ≤ m) :
    IsNoetherian Rᵐᵒᵖ R ∧ Module.DevLE Rᵐᵒᵖ m R ∧ Module.DevLEOmega Rᵐᵒᵖ R :=
  ⟨S.isNoetherian_right, S.devLE_right m hm,
    S.devLEOmega_right (ringKrullDim_ne_top_of_le hm)⟩

/-- **Filtered rings: (N), (Z) and `Kdim ≤ m` on both sides.** Let `R` be a
simple `k`-algebra, `k` an infinite field, with a symbol `S` onto a commutative
Noetherian graded algebra of Krull dimension at most `m`. Then `R` is right
Noetherian with infinite centre and right deviation at most `m` and at most
`ω`; the same holds for `Rᵐᵒᵖ`, using the opposite filtration and the opposite
symbol. -/
theorem filtered_hypotheses [Infinite k] [IsSimpleRing R] [IsNoetherianRing G]
    [GradedAlgebra 𝒜] {φ : RingFiltration k R} (S : φ.GradedSymbol 𝒜) {m : ℕ}
    (hm : ringKrullDim G ≤ m) :
    (IsNoetherian Rᵐᵒᵖ R ∧ Infinite (Subring.center R) ∧
        Module.DevLE Rᵐᵒᵖ m R ∧ Module.DevLEOmega Rᵐᵒᵖ R) ∧
      (IsNoetherian Rᵐᵒᵖᵐᵒᵖ Rᵐᵒᵖ ∧ Infinite (Subring.center Rᵐᵒᵖ) ∧
        Module.DevLE Rᵐᵒᵖᵐᵒᵖ m Rᵐᵒᵖ ∧ Module.DevLEOmega Rᵐᵒᵖᵐᵒᵖ Rᵐᵒᵖ) :=
  ⟨⟨(right_side S hm).1, infinite_subring_center k R, (right_side S hm).2⟩,
    ⟨(right_side S.opposite hm).1, infinite_subring_center k Rᵐᵒᵖ,
      (right_side S.opposite hm).2⟩⟩

end Hypotheses

section Conclusions

variable {k : Type*} [Field k] [Infinite k] {R : Type u} [Ring R] [IsSimpleRing R]
  [Algebra k R]
variable {G : Type*} [CommRing G] [Algebra k G] {𝒜 : ℕ → Submodule k G}

omit [IsSimpleRing R] in
/-- Under (H_all), every cyclic submodule `uR` killed on the right by a regular
element has finite deviation: `uR` is a quotient of `R / sR`. -/
theorem devLE_span_of_torsion {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]
    (hall : PrincipalQuotientsFinite R) {u : M} (hu : ∃ s ∈ R⁰, op s • u = 0) :
    ∃ N, Module.DevLE Rᵐᵒᵖ N (Submodule.span Rᵐᵒᵖ {u}) := by
  obtain ⟨s, hs, hsu⟩ := hu
  obtain ⟨N, hN⟩ := hall s hs
  exact ⟨N, (devLE_quotient_ker_cyclicMap_iff N u).mp
    (devLE_quotient_of_le hN (principalRightIdeal_le (X := LinearMap.ker (cyclicMap u)) hsu))⟩

/-- **Theorem A, both sides.** Let `R` be as in `filtered_hypotheses`. For every
regular `d`, every nonzero `a` and every `B` there are `H, U, V` with
`1 = d U + (B + H a) d V`, in `R` and in `Rᵐᵒᵖ` (the left form
`1 = U d + V d (B + a H)` of `R`). -/
theorem filtered_theoremA [IsNoetherianRing G] [GradedAlgebra 𝒜] {φ : RingFiltration k R}
    (S : φ.GradedSymbol 𝒜) {m : ℕ} (hm : ringKrullDim G ≤ m) :
    (∀ d a B : R, d ∈ R⁰ → a ≠ 0 → ∃ H U V : R, 1 = d * U + (B + H * a) * d * V) ∧
      (∀ d a B : Rᵐᵒᵖ, d ∈ Rᵐᵒᵖ⁰ → a ≠ 0 →
        ∃ H U V : Rᵐᵒᵖ, 1 = d * U + (B + H * a) * d * V) := by
  obtain ⟨⟨hN, -, -, hO⟩, ⟨hN', -, -, hO'⟩⟩ := filtered_hypotheses S hm
  have := hN
  have := hN'
  exact ⟨fun d a B hd ha => fixed_anchor_of_devLE_omega (k := k) hO hd ha B,
    fun d a B hd ha => fixed_anchor_of_devLE_omega (k := k) hO' hd ha B⟩

/-- **Theorem A', both sides.** For every right ideal `I` of `R` containing a
regular element, every `x` and every nonzero `t` there is `H` with
`I + (x + H t) R = R`; the same holds for `Rᵐᵒᵖ`. -/
theorem filtered_fixedIdeal [IsNoetherianRing G] [GradedAlgebra 𝒜] {φ : RingFiltration k R}
    (S : φ.GradedSymbol 𝒜) {m : ℕ} (hm : ringKrullDim G ≤ m) :
    (∀ I : Submodule Rᵐᵒᵖ R, (∃ s ∈ I, s ∈ R⁰) → ∀ x t : R, t ≠ 0 →
        ∃ H : R, I ⊔ principalRightIdeal (x + H * t) = ⊤) ∧
      (∀ I : Submodule Rᵐᵒᵖᵐᵒᵖ Rᵐᵒᵖ, (∃ s ∈ I, s ∈ Rᵐᵒᵖ⁰) → ∀ x t : Rᵐᵒᵖ, t ≠ 0 →
        ∃ H : Rᵐᵒᵖ, I ⊔ principalRightIdeal (x + H * t) = ⊤) := by
  obtain ⟨⟨hN, -, -, hO⟩, ⟨hN', -, -, hO'⟩⟩ := filtered_hypotheses S hm
  have := hN
  have := hN'
  exact ⟨fun I hreg x t ht => by
      obtain ⟨H, hH⟩ := fixed_ideal_of_devLE_omega (k := k) hO hreg x ht
      exact ⟨H, hH⟩,
    fun I hreg x t ht => by
      obtain ⟨H, hH⟩ := fixed_ideal_of_devLE_omega (k := k) hO' hreg x ht
      exact ⟨H, hH⟩⟩

/-- **Corollary C.1, both sides.** Every finitely generated Goldie-torsion right
module `M` over `R` (and over `Rᵐᵒᵖ`) satisfies: for every `x ∈ M` and every
nonzero `t` there is `h ∈ M` with `M = (x + h t) R`. Also, for Goldie-torsion
elements `c, u` of `M` and every nonzero `t` there is `H` with
`cR + uR = (c + u H t) R`. -/
theorem filtered_prescribedCyclic [IsNoetherianRing G] [GradedAlgebra 𝒜] {φ : RingFiltration k R}
    (S : φ.GradedSymbol 𝒜) {m : ℕ} (hm : ringKrullDim G ≤ m) :
    ((∀ (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M],
        IsGoldieTorsion R M → ∀ (x : M) (t : R), t ≠ 0 →
          ∃ h : M, Submodule.span Rᵐᵒᵖ {x + op t • h} = ⊤) ∧
      (∀ (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] (c u : M),
        (∃ s ∈ R⁰, op s • c = 0) → (∃ s ∈ R⁰, op s • u = 0) → ∀ t : R, t ≠ 0 →
          ∃ H : R, Submodule.span Rᵐᵒᵖ {c, u} = Submodule.span Rᵐᵒᵖ {c + op (H * t) • u})) ∧
    ((∀ (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖᵐᵒᵖ M],
        IsGoldieTorsion Rᵐᵒᵖ M → ∀ (x : M) (t : Rᵐᵒᵖ), t ≠ 0 →
          ∃ h : M, Submodule.span Rᵐᵒᵖᵐᵒᵖ {x + op t • h} = ⊤) ∧
      (∀ (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖᵐᵒᵖ M] (c u : M),
        (∃ s ∈ Rᵐᵒᵖ⁰, op s • c = 0) → (∃ s ∈ Rᵐᵒᵖ⁰, op s • u = 0) → ∀ t : Rᵐᵒᵖ, t ≠ 0 →
          ∃ H : Rᵐᵒᵖ, Submodule.span Rᵐᵒᵖᵐᵒᵖ {c, u} =
            Submodule.span Rᵐᵒᵖᵐᵒᵖ {c + op (H * t) • u})) := by
  obtain ⟨⟨hN, -, -, hO⟩, ⟨hN', -, -, hO'⟩⟩ := filtered_hypotheses S hm
  have := hN
  have := hN'
  refine ⟨⟨fun M _ _ _ htor x t ht => prescribed_cyclic_of_devLE_omega (k := k) hO htor x ht,
    fun M _ _ c u hc hu t ht => ?_⟩,
    ⟨fun M _ _ _ htor x t ht => prescribed_cyclic_of_devLE_omega (k := k) hO' htor x ht,
    fun M _ _ c u hc hu t ht => ?_⟩⟩
  · obtain ⟨N, hN⟩ := devLE_span_of_torsion (principalQuotientsFinite_of_devLE_omega hO) hu
    exact span_pair_eq_span_affine (k := k) c u hc hu ⟨N, hN⟩ ht
  · obtain ⟨N, hN⟩ := devLE_span_of_torsion (principalQuotientsFinite_of_devLE_omega hO') hu
    exact span_pair_eq_span_affine (k := k) c u hc hu ⟨N, hN⟩ ht

/-- **Corollary C.2, both sides.** Let `I` be a right ideal of `R` and `a ∈ I`
with `aQ = IQ`, that is every `y ∈ I` has a regular `s` with `y s ∈ aR`. Then for
every `y ∈ I` and nonzero `t` there is `h ∈ I` with `I = aR + (y + h t) R`, and
every right ideal of `R` is generated by two elements; the same holds for
`Rᵐᵒᵖ`. -/
theorem filtered_twoGenerated [IsNoetherianRing G] [GradedAlgebra 𝒜] {φ : RingFiltration k R}
    (S : φ.GradedSymbol 𝒜) {m : ℕ} (hm : ringKrullDim G ≤ m) :
    ((∀ (I : Submodule Rᵐᵒᵖ R) (a : R), a ∈ I →
        (∀ y ∈ I, ∃ s ∈ R⁰, y * s ∈ principalRightIdeal a) →
        ∀ y ∈ I, ∀ t : R, t ≠ 0 →
          ∃ h ∈ I, I = principalRightIdeal a ⊔ principalRightIdeal (y + h * t)) ∧
      ∀ I : Submodule Rᵐᵒᵖ R, ∃ a b : R, I = principalRightIdeal a ⊔ principalRightIdeal b) ∧
    ((∀ (I : Submodule Rᵐᵒᵖᵐᵒᵖ Rᵐᵒᵖ) (a : Rᵐᵒᵖ), a ∈ I →
        (∀ y ∈ I, ∃ s ∈ Rᵐᵒᵖ⁰, y * s ∈ principalRightIdeal a) →
        ∀ y ∈ I, ∀ t : Rᵐᵒᵖ, t ≠ 0 →
          ∃ h ∈ I, I = principalRightIdeal a ⊔ principalRightIdeal (y + h * t)) ∧
      ∀ I : Submodule Rᵐᵒᵖᵐᵒᵖ Rᵐᵒᵖ, ∃ a b : Rᵐᵒᵖ,
        I = principalRightIdeal a ⊔ principalRightIdeal b) := by
  obtain ⟨⟨hN, -, -, hO⟩, ⟨hN', -, -, hO'⟩⟩ := filtered_hypotheses S hm
  have := hN
  have := hN'
  exact ⟨⟨fun I a haI hIa y hyI t ht => by
        obtain ⟨h, hhI, hI⟩ := two_generated_prescribed (k := k)
          (principalQuotientsFinite_of_devLE_omega hO) haI hIa hyI ht
        exact ⟨h, hhI, hI⟩,
      fun I => two_generated (k := k) (principalQuotientsFinite_of_devLE_omega hO) I⟩,
    ⟨fun I a haI hIa y hyI t ht => by
        obtain ⟨h, hhI, hI⟩ := two_generated_prescribed (k := k)
          (principalQuotientsFinite_of_devLE_omega hO') haI hIa hyI ht
        exact ⟨h, hhI, hI⟩,
      fun I => two_generated (k := k) (principalQuotientsFinite_of_devLE_omega hO') I⟩⟩

end Conclusions

end GeneralizedStafford
