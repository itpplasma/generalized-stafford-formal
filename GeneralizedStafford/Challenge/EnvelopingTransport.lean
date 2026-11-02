module

public import GeneralizedStafford.Challenge.FilteredTransport
public import GeneralizedStafford.Enveloping

@[expose] public section

/-!
# Challenge transport: simple quotients of enveloping algebras

The definitions of the enveloping-algebra section of `GeneralizedStaffordChallenge.lean`
(identical copy `Challenge.lean`) are restated verbatim below, in the same namespace and
under the same names. The conclusion predicates (`FixedAnchorProperty`, ...) and the
bridge lemmas are those of `GeneralizedStafford/Challenge/FilteredTransport.lean`, which
this file imports; they are the same declarations used for the filtered rings.

Each compared enveloping theorem `<name>` of the challenge is proved here as
`<name>_proof`; `GeneralizedStaffordSolution.lean` restates it under its challenge name.
`envelopingSide` applies the library theorem `GeneralizedStafford.enveloping_hypotheses`
and translates its deviation statements into the challenge form.
-/

universe u v

namespace GeneralizedStaffordChallenge

open MulOpposite

/-! ## Definitions (verbatim from the challenge) -/

/-- **Simple quotients of enveloping algebras, hypotheses.** For a finite-dimensional
Lie algebra `𝔤` over an infinite field `k` and a simple quotient `R` of `U(𝔤)`,
`R` and `Rᵐᵒᵖ` are Noetherian, have infinite centre and have Krull dimension at most
`dim 𝔤`. -/
def EnvelopingHypothesesStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (L : Type u) [LieRing L] [LieAlgebra k L]
    [FiniteDimensional k L] (R : Type u) [Ring R] [Algebra k R] [IsSimpleRing R]
    (f : UniversalEnvelopingAlgebra k L →ₐ[k] R), Function.Surjective f →
    (IsNoetherian Rᵐᵒᵖ R ∧ Infinite (Subring.center R) ∧
        DevDimLE R R (Module.finrank k L)) ∧
      (IsNoetherian Rᵐᵒᵖᵐᵒᵖ Rᵐᵒᵖ ∧ Infinite (Subring.center Rᵐᵒᵖ) ∧
        DevDimLE Rᵐᵒᵖ Rᵐᵒᵖ (Module.finrank k L))

/-- **Simple quotients of enveloping algebras, Theorem A.** Under the hypotheses of
`EnvelopingHypothesesStatement`, Theorem A holds for `R` (right form
`1 = d U + (B + H a) d V`) and for `Rᵐᵒᵖ` (left form `1 = U d + V d (B + a H)` of `R`). -/
def EnvelopingTheoremAStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (L : Type u) [LieRing L] [LieAlgebra k L]
    [FiniteDimensional k L] (R : Type u) [Ring R] [Algebra k R] [IsSimpleRing R]
    (f : UniversalEnvelopingAlgebra k L →ₐ[k] R), Function.Surjective f →
    FixedAnchorProperty R ∧ FixedAnchorProperty Rᵐᵒᵖ

/-- **Simple quotients of enveloping algebras, Theorem A'.** Under the hypotheses of
`EnvelopingHypothesesStatement`, Theorem A' holds for `R` and for `Rᵐᵒᵖ`. -/
def EnvelopingFixedIdealStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (L : Type u) [LieRing L] [LieAlgebra k L]
    [FiniteDimensional k L] (R : Type u) [Ring R] [Algebra k R] [IsSimpleRing R]
    (f : UniversalEnvelopingAlgebra k L →ₐ[k] R), Function.Surjective f →
    FixedIdealProperty R ∧ FixedIdealProperty Rᵐᵒᵖ

/-- **Simple quotients of enveloping algebras, Corollary C.1.** Under the hypotheses of
`EnvelopingHypothesesStatement`, the prescribed-generator and stable forms of C.1 hold for
`R` and for `Rᵐᵒᵖ`. -/
def EnvelopingPrescribedCyclicStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (L : Type u) [LieRing L] [LieAlgebra k L]
    [FiniteDimensional k L] (R : Type u) [Ring R] [Algebra k R] [IsSimpleRing R]
    (f : UniversalEnvelopingAlgebra k L →ₐ[k] R), Function.Surjective f →
    (PrescribedCyclicProperty.{u, v} R ∧ StablyCyclicProperty.{u, v} R) ∧
      (PrescribedCyclicProperty.{u, v} Rᵐᵒᵖ ∧ StablyCyclicProperty.{u, v} Rᵐᵒᵖ)

/-- **Simple quotients of enveloping algebras, Corollary C.2.** Under the hypotheses of
`EnvelopingHypothesesStatement`, the two-generation statements of C.2 hold for `R` and for
`Rᵐᵒᵖ`. -/
def EnvelopingTwoGeneratedStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (L : Type u) [LieRing L] [LieAlgebra k L]
    [FiniteDimensional k L] (R : Type u) [Ring R] [Algebra k R] [IsSimpleRing R]
    (f : UniversalEnvelopingAlgebra k L →ₐ[k] R), Function.Surjective f →
    TwoGeneratedProperty R ∧ TwoGeneratedProperty Rᵐᵒᵖ

/-! ## Bridge: (N), (Z), `Kdim ≤ dim 𝔤` and (H_omega) on both sides -/

/-- Both sides of a simple quotient of `U(𝔤)` satisfy (N), (Z), the deviation bound
`Kdim ≤ dim 𝔤` and (H_omega), from `GeneralizedStafford.enveloping_hypotheses`. -/
theorem envelopingSide {k L R : Type u} [Field k] [Infinite k] [LieRing L] [LieAlgebra k L]
    [FiniteDimensional k L] [Ring R] [Algebra k R] [IsSimpleRing R]
    (f : UniversalEnvelopingAlgebra k L →ₐ[k] R) (hf : Function.Surjective f) :
    (IsNoetherian Rᵐᵒᵖ R ∧ Infinite (Subring.center R) ∧
        DevDimLE R R (Module.finrank k L) ∧ HOmega R) ∧
      (IsNoetherian Rᵐᵒᵖᵐᵒᵖ Rᵐᵒᵖ ∧ Infinite (Subring.center Rᵐᵒᵖ) ∧
        DevDimLE Rᵐᵒᵖ Rᵐᵒᵖ (Module.finrank k L) ∧ HOmega Rᵐᵒᵖ) := by
  obtain ⟨⟨hN1, hZ1, hD1, hO1⟩, ⟨hN2, hZ2, hD2, hO2⟩⟩ :=
    GeneralizedStafford.enveloping_hypotheses f hf
  exact ⟨⟨hN1, hZ1, (devDimLE_iff _).mpr hD1, hOmega_iff.mpr hO1⟩,
    ⟨hN2, hZ2, (devDimLE_iff _).mpr hD2, hOmega_iff.mpr hO2⟩⟩

/-! ## Proofs of the compared enveloping statements -/

/-- Simple quotients of enveloping algebras: (N), (Z) and `Kdim ≤ dim 𝔤` on both sides. -/
theorem envelopingHypotheses_proof : EnvelopingHypothesesStatement.{u} := by
  intro k _ _ L _ _ _ R _ _ _ f hf
  obtain ⟨⟨hN, hZ, hD, -⟩, ⟨hN', hZ', hD', -⟩⟩ := envelopingSide f hf
  exact ⟨⟨hN, hZ, hD⟩, ⟨hN', hZ', hD'⟩⟩

/-- Simple quotients of enveloping algebras: Theorem A, right and left forms. -/
theorem envelopingTheoremA_proof : EnvelopingTheoremAStatement.{u} := by
  intro k _ _ L _ _ _ R _ _ _ f hf
  obtain ⟨⟨hN, hZ, -, hO⟩, ⟨hN', hZ', -, hO'⟩⟩ := envelopingSide f hf
  have := hN
  have := hZ
  have := hN'
  have := hZ'
  exact ⟨fixedAnchorProperty_of_omega hO, fixedAnchorProperty_of_omega hO'⟩

/-- Simple quotients of enveloping algebras: Theorem A' on both sides. -/
theorem envelopingFixedIdeal_proof : EnvelopingFixedIdealStatement.{u} := by
  intro k _ _ L _ _ _ R _ _ _ f hf
  obtain ⟨⟨hN, hZ, -, hO⟩, ⟨hN', hZ', -, hO'⟩⟩ := envelopingSide f hf
  have := hN
  have := hZ
  have := hN'
  have := hZ'
  exact ⟨fixedIdealProperty_of_omega hO, fixedIdealProperty_of_omega hO'⟩

/-- Simple quotients of enveloping algebras: Corollary C.1 (prescribed and stable) on both
sides. -/
theorem envelopingPrescribedCyclic_proof : EnvelopingPrescribedCyclicStatement.{u, v} := by
  intro k _ _ L _ _ _ R _ _ _ f hf
  obtain ⟨⟨hN, hZ, -, hO⟩, ⟨hN', hZ', -, hO'⟩⟩ := envelopingSide f hf
  have := hN
  have := hZ
  have := hN'
  have := hZ'
  exact ⟨⟨prescribedCyclicProperty_of_omega hO, stablyCyclic_of_omega hO⟩,
    ⟨prescribedCyclicProperty_of_omega hO', stablyCyclic_of_omega hO'⟩⟩

/-- Simple quotients of enveloping algebras: Corollary C.2 on both sides. -/
theorem envelopingTwoGenerated_proof : EnvelopingTwoGeneratedStatement.{u} := by
  intro k _ _ L _ _ _ R _ _ _ f hf
  obtain ⟨⟨hN, hZ, -, hO⟩, ⟨hN', hZ', -, hO'⟩⟩ := envelopingSide f hf
  have := hN
  have := hZ
  have := hN'
  have := hZ'
  exact ⟨twoGeneratedProperty_of_omega hO, twoGeneratedProperty_of_omega hO'⟩

end GeneralizedStaffordChallenge
