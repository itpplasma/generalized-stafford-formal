module

public import GeneralizedStafford.ConsequencesForU

@[expose] public section

/-!
# The universal general filtered Stafford statement

The supplied data encode a unital nonnegative filtration and its actual
associated graded algebra. They contain no source-selection hypothesis.
-/

namespace GeneralizedStafford

universe u v w

/-- The affine same-divisor statement for the general filtered class. -/
def Statement : Prop :=
  ∀ (k : Type u) (U : Type v) (G : Type w)
    [Field k] [Infinite k] [Ring U] [Algebra k U] [IsSimpleRing U]
    [CommRing G] [IsDomain G] [IsNoetherianRing G] [Algebra k G]
    (𝒜 : ℕ → Submodule k G) [GradedAlgebra 𝒜]
    (_D : FilteredAlgebraData k U G 𝒜),
    ringKrullDim G < ⊤ →
      ∀ d a : U, d ≠ 0 → a ≠ 0 → ∀ B : U,
        ∃ H R S : U, 1 = d * R + (B + H * a) * d * S

/-- The full affine theorem, derived from the source-construction proof. -/
theorem universalStatement : Statement.{u, v, w} := by
  intro k U G _ _ _ _ _ _ _ _ _ 𝒜 _ D hdim d a hd ha B
  exact D.targetA hdim d a hd ha B

end GeneralizedStafford
