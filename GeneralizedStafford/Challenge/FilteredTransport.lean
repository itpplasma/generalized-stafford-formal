import GeneralizedStafford.Challenge.Transport
import GeneralizedStafford.Filtered
import AlgebraicAnalysis.Filtration.SymbolDomain

/-!
# Challenge transport: filtered rings

The definitions of the filtered-ring section of `GeneralizedStaffordChallenge.lean`
(identical copy `Challenge.lean`) are restated verbatim below, in the same
namespace and under the same names. The definitions of the earlier sections are
those of `GeneralizedStafford/Challenge/Transport.lean`, which this file imports.

Each compared filtered theorem `<name>` of the challenge is proved here as
`<name>_proof`; `GeneralizedStaffordSolution.lean` restates it under its challenge
name. The bridge `toAA` and `symbolToAA` translates a challenge filtration and
symbol into AlgebraicAnalysis' `RingFiltration` and `GradedSymbol`, and
`filtered_side` applies the library theorem `GeneralizedStafford.filtered_hypotheses`
to both sides.
-/

universe u v

namespace GeneralizedStaffordChallenge

open MulOpposite

/-! ## Definitions (verbatim from the challenge) -/

section Conclusions

variable (R : Type u) [Ring R]

/-- The conclusion of Theorem A for every regular anchor (Corollary B): for
every regular `d`, every nonzero `a` and every `B` there are `H, U, V` with
`1 = d U + (B + H a) d V`. -/
def FixedAnchorProperty : Prop :=
  ∀ d a B : R, IsRegularElement d → a ≠ 0 →
    ∃ H U V : R, 1 = d * U + (B + H * a) * d * V

/-- The conclusion of Theorem A' for every right ideal containing a regular
element (Corollary B): `I + (x + H t)R = R` for some `H`, for every `x` and
every nonzero `t`. -/
def FixedIdealProperty : Prop :=
  ∀ I : Submodule Rᵐᵒᵖ R, (∃ s ∈ I, IsRegularElement s) →
    ∀ x t : R, t ≠ 0 → ∃ H : R, I ⊔ Submodule.span Rᵐᵒᵖ {x + H * t} = ⊤

/-- (C.1), prescribed generator: every finitely generated Goldie-torsion right
module `M` satisfies `M = (x + h t)R` for some `h`, for every `x ∈ M` and every
nonzero `t ∈ R`. -/
def PrescribedCyclicProperty : Prop :=
  ∀ (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M],
    IsGoldieTorsion R M →
    ∀ (x : M) (t : R), t ≠ 0 → ∃ h : M, Submodule.span Rᵐᵒᵖ {x + op t • h} = ⊤

/-- (C.1), stable cyclicity: for Goldie-torsion elements `c, u` of a right
module and every nonzero `t` there is `H` with `cR + uR = (c + u H t)R`. -/
def StablyCyclicProperty : Prop :=
  ∀ (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] (c u : M),
    (∃ s : R, IsRegularElement s ∧ op s • c = 0) →
    (∃ s : R, IsRegularElement s ∧ op s • u = 0) →
    ∀ t : R, t ≠ 0 →
      ∃ H : R, Submodule.span Rᵐᵒᵖ {c, u} = Submodule.span Rᵐᵒᵖ {c + op (H * t) • u}

/-- (C.2): every right ideal `I` is `aR + (y + h t)R` for every `a ∈ I` with
`aQ = IQ` (every `y' ∈ I` has a regular `s` with `y' s ∈ aR`), every `y ∈ I`
and every nonzero `t`, with some `h ∈ I`; and every right ideal is generated
by two elements. -/
def TwoGeneratedProperty : Prop :=
  (∀ (I : Submodule Rᵐᵒᵖ R) (a : R), a ∈ I →
    (∀ y ∈ I, ∃ s : R, IsRegularElement s ∧ y * s ∈ Submodule.span Rᵐᵒᵖ {a}) →
    ∀ y ∈ I, ∀ t : R, t ≠ 0 →
      ∃ h ∈ I, I = Submodule.span Rᵐᵒᵖ {a} ⊔ Submodule.span Rᵐᵒᵖ {y + h * t}) ∧
  ∀ I : Submodule Rᵐᵒᵖ R, ∃ a b : R, I = Submodule.span Rᵐᵒᵖ {a, b}

end Conclusions

/-- An exhaustive increasing filtration `F₀ ⊆ F₁ ⊆ ⋯` of the `k`-algebra `R`
by `k`-subspaces with `1 ∈ F₀` and `Fᵢ Fⱼ ⊆ Fᵢ₊ⱼ`. -/
structure RingFiltration (k R : Type u) [CommRing k] [Ring R] [Algebra k R] where
  /-- The filtration pieces `Fₙ`. -/
  F : ℕ → Submodule k R
  /-- `Fᵢ ⊆ Fⱼ` for `i ≤ j`. -/
  mono : Monotone F
  /-- `1 ∈ F₀`. -/
  one_mem : (1 : R) ∈ F 0
  /-- `Fᵢ Fⱼ ⊆ Fᵢ₊ⱼ`. -/
  mul_mem : ∀ {i j : ℕ} {x y : R}, x ∈ F i → y ∈ F j → x * y ∈ F (i + j)
  /-- The filtration is exhaustive. -/
  exhaustive : ∀ x : R, ∃ n, x ∈ F n

/-- The previous filtration piece `Fₙ₋₁`, with `F₋₁ = 0`. -/
def RingFiltration.below {k R : Type u} [CommRing k] [Ring R] [Algebra k R]
    (φ : RingFiltration k R) : ℕ → Submodule k R
  | 0 => ⊥
  | n + 1 => φ.F n

/-- Principal-symbol data identifying `gr R = ⨁ₙ Fₙ/Fₙ₋₁` with the commutative
graded algebra `G = ⨁ₙ 𝒜ₙ`: surjective `k`-linear maps `grₙ : Fₙ → 𝒜ₙ` with
kernel `Fₙ₋₁` that multiply symbols. -/
structure GradedSymbol {k R G : Type u} [CommRing k] [Ring R] [Algebra k R] [CommRing G]
    [Algebra k G] (φ : RingFiltration k R) (𝒜 : ℕ → Submodule k G) where
  /-- The degree-`n` symbol map `Fₙ → 𝒜ₙ`. -/
  gr : ∀ n, φ.F n →ₗ[k] 𝒜 n
  /-- Every homogeneous element of degree `n` is a symbol. -/
  gr_surjective : ∀ n, Function.Surjective (gr n)
  /-- The kernel of `grₙ` is `Fₙ₋₁`. -/
  gr_eq_zero_iff : ∀ n (x : φ.F n), gr n x = 0 ↔ (x : R) ∈ φ.below n
  /-- Symbols multiply: `gr_{i+j}(x y) = grᵢ(x) grⱼ(y)`. -/
  gr_mul : ∀ i j (x : φ.F i) (y : φ.F j),
    ((gr (i + j) ⟨x * y, φ.mul_mem x.2 y.2⟩ : 𝒜 (i + j)) : G) =
      (gr i x : G) * (gr j y : G)

/-- `R` has an exhaustive filtration whose associated graded ring is a
commutative Noetherian ring of Krull dimension at most `m`. -/
def HasCommNoetherianGr (k R : Type u) [CommRing k] [Ring R] [Algebra k R] (m : ℕ) :
    Prop :=
  ∃ (φ : RingFiltration k R) (G : Type u) (_ : CommRing G) (_ : Algebra k G)
    (𝒜 : ℕ → Submodule k G) (_ : GradedAlgebra 𝒜),
    Nonempty (GradedSymbol φ 𝒜) ∧ IsNoetherianRing G ∧ ringKrullDim G ≤ m

/-- `R` has an exhaustive filtration whose associated graded ring is a
commutative Noetherian **domain** of finite Krull dimension. -/
def HasCommNoetherianDomainGr (k R : Type u) [CommRing k] [Ring R] [Algebra k R] :
    Prop :=
  ∃ (φ : RingFiltration k R) (G : Type u) (_ : CommRing G) (_ : Algebra k G)
    (𝒜 : ℕ → Submodule k G) (_ : GradedAlgebra 𝒜),
    Nonempty (GradedSymbol φ 𝒜) ∧ IsNoetherianRing G ∧ IsDomain G ∧ ringKrullDim G < ⊤

/-- **Theorem A, both forms (filtered rings).** Let `k` be an infinite field and
`R` a simple `k`-algebra with an exhaustive filtration such that `gr R` is
commutative Noetherian of Krull dimension at most `m`. Then Theorem A holds for
`R` (right form `1 = d U + (B + H a) d V`) and for `Rᵐᵒᵖ` (left form
`1 = U d + V d (B + a H)` of `R`). -/
def FilteredTheoremAStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (R : Type u) [Ring R] [Algebra k R]
    [IsSimpleRing R] (m : ℕ), HasCommNoetherianGr k R m →
    FixedAnchorProperty R ∧ FixedAnchorProperty Rᵐᵒᵖ

/-- **Theorem A', both sides (filtered rings).** Under the hypotheses of
`FilteredTheoremAStatement`, Theorem A' holds for `R` and for `Rᵐᵒᵖ`. -/
def FilteredFixedIdealStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (R : Type u) [Ring R] [Algebra k R]
    [IsSimpleRing R] (m : ℕ), HasCommNoetherianGr k R m →
    FixedIdealProperty R ∧ FixedIdealProperty Rᵐᵒᵖ

/-- **Corollary C.1, both sides (filtered rings).** Under the hypotheses of
`FilteredTheoremAStatement`, the prescribed-generator and stable forms of C.1
hold for `R` and for `Rᵐᵒᵖ`. -/
def FilteredPrescribedCyclicStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (R : Type u) [Ring R] [Algebra k R]
    [IsSimpleRing R] (m : ℕ), HasCommNoetherianGr k R m →
    (PrescribedCyclicProperty.{u, v} R ∧ StablyCyclicProperty.{u, v} R) ∧
      (PrescribedCyclicProperty.{u, v} Rᵐᵒᵖ ∧ StablyCyclicProperty.{u, v} Rᵐᵒᵖ)

/-- **Corollary C.2, both sides (filtered rings).** Under the hypotheses of
`FilteredTheoremAStatement`, the two-generation statements of C.2 hold for `R`
and for `Rᵐᵒᵖ`. -/
def FilteredTwoGeneratedStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (R : Type u) [Ring R] [Algebra k R]
    [IsSimpleRing R] (m : ℕ), HasCommNoetherianGr k R m →
    TwoGeneratedProperty R ∧ TwoGeneratedProperty Rᵐᵒᵖ

/-- **Proposition (filtered rings), hypotheses.** Let `k` be an infinite field
and `R` a simple `k`-algebra with an exhaustive filtration such that `gr R` is
commutative Noetherian of Krull dimension at most `m`. Then `R` and `Rᵐᵒᵖ`
satisfy (N), (Z) and `Kdim ≤ m`. (`Rᵐᵒᵖ` is simple by Mathlib's instance.) -/
def FilteredHypothesesStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (R : Type u) [Ring R] [Algebra k R]
    [IsSimpleRing R] (m : ℕ), HasCommNoetherianGr k R m →
    (IsNoetherian Rᵐᵒᵖ R ∧ Infinite (Subring.center R) ∧ DevDimLE R R m) ∧
    (IsNoetherian Rᵐᵒᵖᵐᵒᵖ Rᵐᵒᵖ ∧ Infinite (Subring.center Rᵐᵒᵖ) ∧ DevDimLE Rᵐᵒᵖ Rᵐᵒᵖ m)

/-- **Simple quantizations.** If `R` is a simple algebra over an infinite field
`k` with an exhaustive filtration whose associated graded ring is a commutative
Noetherian domain of finite Krull dimension (for instance `gr R ≅ ℂ[X]` for an
irreducible affine variety `X`), then for every nonzero `d` and `a` and every
`B` there are `H, U, V` with `1 = d U + (B + H a) d V`, and the same holds in
`Rᵐᵒᵖ`, i.e. `1 = U d + V d (B + a H)` in `R`. -/
def FilteredDomainStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (R : Type u) [Ring R] [Algebra k R]
    [IsSimpleRing R], HasCommNoetherianDomainGr k R →
    (∀ d a B : R, d ≠ 0 → a ≠ 0 → ∃ H U V : R, 1 = d * U + (B + H * a) * d * V) ∧
    (∀ d a B : R, d ≠ 0 → a ≠ 0 → ∃ H U V : R, 1 = U * d + V * d * (B + a * H))

/-! ## Bridge: challenge filtrations and symbols to AlgebraicAnalysis -/

/-- The challenge filtration as an AlgebraicAnalysis filtration. -/
def toAA {k R : Type u} [CommRing k] [Ring R] [Algebra k R] (φ : RingFiltration k R) :
    AlgebraicAnalysis.RingFiltration k R where
  F := φ.F
  mono := φ.mono
  one_mem := φ.one_mem
  mul_le _ _ := Submodule.mul_le.mpr fun _ hx _ hy => φ.mul_mem hx hy
  exhaustive := eq_top_iff.mpr fun x _ =>
    let ⟨n, hn⟩ := φ.exhaustive x; Submodule.mem_iSup_of_mem n hn

theorem below_toAA {k R : Type u} [CommRing k] [Ring R] [Algebra k R] (φ : RingFiltration k R)
    (n : ℕ) : (toAA φ).below n = φ.below n := by
  cases n <;> rfl

/-- The challenge symbol as an AlgebraicAnalysis symbol of `toAA φ`. -/
def symbolToAA {k R G : Type u} [CommRing k] [Ring R] [Algebra k R] [CommRing G] [Algebra k G]
    {φ : RingFiltration k R} {𝒜 : ℕ → Submodule k G} (S : GradedSymbol φ 𝒜) :
    AlgebraicAnalysis.RingFiltration.GradedSymbol (toAA φ) 𝒜 where
  gr := S.gr
  gr_surjective := S.gr_surjective
  gr_eq_zero_iff n x := by rw [below_toAA]; exact S.gr_eq_zero_iff n x
  gr_mul := S.gr_mul

/-- Both sides of a challenge filtered ring satisfy (N), (Z), the deviation
bound `Kdim ≤ m` and (H_omega), from `GeneralizedStafford.filtered_hypotheses`. -/
theorem filtered_side {k R : Type u} [Field k] [Infinite k] [Ring R] [Algebra k R]
    [IsSimpleRing R] {m : ℕ} (h : HasCommNoetherianGr k R m) :
    (IsNoetherian Rᵐᵒᵖ R ∧ Infinite (Subring.center R) ∧ DevDimLE R R m ∧ HOmega R) ∧
      (IsNoetherian Rᵐᵒᵖᵐᵒᵖ Rᵐᵒᵖ ∧ Infinite (Subring.center Rᵐᵒᵖ) ∧
        DevDimLE Rᵐᵒᵖ Rᵐᵒᵖ m ∧ HOmega Rᵐᵒᵖ) := by
  obtain ⟨φ, G, _, _, 𝒜, _, ⟨S⟩, hN, hdim⟩ := h
  have := hN
  obtain ⟨⟨hN1, hZ1, hD1, hO1⟩, ⟨hN2, hZ2, hD2, hO2⟩⟩ :=
    GeneralizedStafford.filtered_hypotheses (symbolToAA S) hdim
  exact ⟨⟨hN1, hZ1, (devDimLE_iff m).mpr hD1, hOmega_iff.mpr hO1⟩,
    ⟨hN2, hZ2, (devDimLE_iff m).mpr hD2, hOmega_iff.mpr hO2⟩⟩

/-! ## Conclusions from (N), (Z) and (H_omega) for one ring -/

/-- Theorem A (right form) from (H_omega), via Corollary B. -/
theorem fixedAnchorProperty_of_omega {R : Type u} [Ring R] [IsSimpleRing R]
    [IsNoetherian Rᵐᵒᵖ R] [Infinite (Subring.center R)] (homega : HOmega R) :
    FixedAnchorProperty R :=
  corollaryB_fixedAnchor_proof.{u} R homega

/-- Theorem A' from (H_omega), via Corollary B. -/
theorem fixedIdealProperty_of_omega {R : Type u} [Ring R] [IsSimpleRing R]
    [IsNoetherian Rᵐᵒᵖ R] [Infinite (Subring.center R)] (homega : HOmega R) :
    FixedIdealProperty R :=
  corollaryB_fixedIdeal_proof.{u} R homega

/-- The stable form of C.1 from (H_omega): under (H_all) a cyclic submodule `uR`
killed by a regular element has finite deviation, and the library lemma applies. -/
theorem stablyCyclic_of_omega {R : Type u} [Ring R] [IsSimpleRing R]
    [IsNoetherian Rᵐᵒᵖ R] [Infinite (Subring.center R)] (homega : HOmega R) :
    StablyCyclicProperty.{u, v} R := by
  intro M _ _ c u hc hu t ht
  have hall : GeneralizedStafford.PrincipalQuotientsFinite R :=
    hAll_iff.mp (hAll_of_omega homega)
  have hc' : ∃ s ∈ nonZeroDivisors R, op s • c = 0 := by
    obtain ⟨s, hs, h⟩ := hc
    exact ⟨s, (isRegular_iff s).mp hs, h⟩
  have hu' : ∃ s ∈ nonZeroDivisors R, op s • u = 0 := by
    obtain ⟨s, hs, h⟩ := hu
    exact ⟨s, (isRegular_iff s).mp hs, h⟩
  obtain ⟨N, hN⟩ := GeneralizedStafford.devLE_span_of_torsion hall hu'
  refine withCentre R _ fun k _ _ _ => ?_
  exact GeneralizedStafford.span_pair_eq_span_affine (k := k) c u hc' hu' ⟨N, hN⟩ ht

/-- (C.1), prescribed generator, from (H_omega). -/
theorem prescribedCyclicProperty_of_omega {R : Type u} [Ring R] [IsSimpleRing R]
    [IsNoetherian Rᵐᵒᵖ R] [Infinite (Subring.center R)] (homega : HOmega R) :
    PrescribedCyclicProperty.{u, v} R :=
  corollaryC1_omega_proof.{u, v} R homega

/-- (C.2) from (H_omega): the prescribed form and the two-generation statement. -/
theorem twoGeneratedProperty_of_omega {R : Type u} [Ring R] [IsSimpleRing R]
    [IsNoetherian Rᵐᵒᵖ R] [Infinite (Subring.center R)] (homega : HOmega R) :
    TwoGeneratedProperty R :=
  ⟨corollaryC2_prescribed_proof.{u} R (hAll_of_omega homega),
    corollaryC2_proof.{u} R (hAll_of_omega homega)⟩

/-! ## Proofs of the compared filtered statements -/

/-- Filtered rings: (N), (Z), `Kdim ≤ m` on both sides, from
`GeneralizedStafford.filtered_hypotheses`. -/
theorem filteredHypotheses_proof : FilteredHypothesesStatement.{u} := by
  intro k _ _ R _ _ _ m h
  obtain ⟨⟨hN, hZ, hD, -⟩, ⟨hN', hZ', hD', -⟩⟩ := filtered_side h
  exact ⟨⟨hN, hZ, hD⟩, ⟨hN', hZ', hD'⟩⟩

/-- Filtered rings: Theorem A, right and left forms. -/
theorem filteredTheoremA_proof : FilteredTheoremAStatement.{u} := by
  intro k _ _ R _ _ _ m h
  obtain ⟨⟨hN, hZ, -, hO⟩, ⟨hN', hZ', -, hO'⟩⟩ := filtered_side h
  have := hN
  have := hZ
  have := hN'
  have := hZ'
  exact ⟨fixedAnchorProperty_of_omega hO, fixedAnchorProperty_of_omega hO'⟩

/-- Filtered rings: Theorem A' on both sides. -/
theorem filteredFixedIdeal_proof : FilteredFixedIdealStatement.{u} := by
  intro k _ _ R _ _ _ m h
  obtain ⟨⟨hN, hZ, -, hO⟩, ⟨hN', hZ', -, hO'⟩⟩ := filtered_side h
  have := hN
  have := hZ
  have := hN'
  have := hZ'
  exact ⟨fixedIdealProperty_of_omega hO, fixedIdealProperty_of_omega hO'⟩

/-- Filtered rings: Corollary C.1 (prescribed and stable) on both sides. -/
theorem filteredPrescribedCyclic_proof : FilteredPrescribedCyclicStatement.{u, v} := by
  intro k _ _ R _ _ _ m h
  obtain ⟨⟨hN, hZ, -, hO⟩, ⟨hN', hZ', -, hO'⟩⟩ := filtered_side h
  have := hN
  have := hZ
  have := hN'
  have := hZ'
  exact ⟨⟨prescribedCyclicProperty_of_omega hO, stablyCyclic_of_omega hO⟩,
    ⟨prescribedCyclicProperty_of_omega hO', stablyCyclic_of_omega hO'⟩⟩

/-- Filtered rings: Corollary C.2 on both sides. -/
theorem filteredTwoGenerated_proof : FilteredTwoGeneratedStatement.{u} := by
  intro k _ _ R _ _ _ m h
  obtain ⟨⟨hN, hZ, -, hO⟩, ⟨hN', hZ', -, hO'⟩⟩ := filtered_side h
  have := hN
  have := hZ
  have := hN'
  have := hZ'
  exact ⟨twoGeneratedProperty_of_omega hO, twoGeneratedProperty_of_omega hO'⟩

/-- A nonzero element of a domain is regular. -/
theorem isRegular_of_ne_zero' {R : Type u} [Ring R] [NoZeroDivisors R] {d : R} (hd : d ≠ 0) :
    IsRegularElement d :=
  ⟨fun _ hx => (mul_eq_zero.mp hx).resolve_left hd, fun _ hx => (mul_eq_zero.mp hx).resolve_right hd⟩

/-- A Krull dimension below `⊤` is bounded by a natural number. -/
theorem exists_nat_le_of_lt_top {G : Type u} [CommRing G] (h : ringKrullDim G < ⊤) :
    ∃ m : ℕ, ringKrullDim G ≤ m := by
  rcases hr : ringKrullDim G with _ | _ | m
  · exact ⟨0, bot_le⟩
  · exact absurd hr h.ne
  · exact ⟨m, le_rfl⟩

/-- Filtered rings with a domain as associated graded ring: Theorem A for every
nonzero anchor, on both sides. The domain structure makes `R` a domain
(AlgebraicAnalysis `GradedSymbol.noZeroDivisors`), so nonzero elements are regular. -/
theorem filteredDomain_proof : FilteredDomainStatement.{u} := by
  intro k _ _ R _ _ _ h
  obtain ⟨φ, G, cG, aG, 𝒜, gA, ⟨S⟩, hN, hD, hlt⟩ := h
  obtain ⟨m, hm⟩ := exists_nat_le_of_lt_top hlt
  have hA : HasCommNoetherianGr k R m := ⟨φ, G, cG, aG, 𝒜, gA, ⟨S⟩, hN, hm⟩
  obtain ⟨⟨hN1, hZ1, -, hO1⟩, ⟨hN2, hZ2, -, hO2⟩⟩ := filtered_side hA
  have := hN1
  have := hZ1
  have := hN2
  have := hZ2
  have : NoZeroDivisors R := (symbolToAA S).noZeroDivisors
  have hright := fixedAnchorProperty_of_omega hO1
  have hleft := fixedAnchorProperty_of_omega hO2
  refine ⟨fun d a B hd ha => hright d a B (isRegular_of_ne_zero' hd) ha, fun d a B hd ha => ?_⟩
  obtain ⟨H, U, V, hUV⟩ := hleft (op d) (op a) (op B)
    (isRegular_of_ne_zero' ((op_ne_zero_iff d).mpr hd)) ((op_ne_zero_iff a).mpr ha)
  refine ⟨unop H, unop U, unop V, ?_⟩
  have h2 := congrArg MulOpposite.unop hUV
  simp only [MulOpposite.unop_add, MulOpposite.unop_mul, MulOpposite.unop_op,
    MulOpposite.unop_one] at h2
  rw [h2, mul_assoc]

end GeneralizedStaffordChallenge
