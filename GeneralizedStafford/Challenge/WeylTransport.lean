import GeneralizedStafford.Challenge.Transport
import GeneralizedStafford.Weyl
import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.FreeAlgebra
import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# Challenge transport: the Weyl algebra statements

The definitions of the Weyl part of `GeneralizedStaffordChallenge.lean` (identical
copy `Challenge.lean`) are restated verbatim below, in the same namespaces and under
the same names, so that the solution never imports the challenge. Each challenge
theorem `<name>` is proved here as `<name>_proof`; `GeneralizedStaffordSolution.lean`
restates it under its challenge name.

The Weyl algebra is `Stafford38Challenge.WeylAlg`, the presented algebra of the
registered challenge. Its proofs are the AlgebraicAnalysis Weyl facts of
`GeneralizedStafford.Weyl`, which use AlgebraicAnalysis' `WeylAlg`; the two are
the same presentation, with the same relation body, so they agree definitionally.
-/

universe u v

/-! ## Weyl algebra: two-generated one-sided ideals

The Weyl algebra `A_n(k)` is the presented algebra of the registered Stafford 3.8
challenge. The definitions `Stafford.freeWeylRelation`, `Stafford.FreeWeyl`,
`Stafford38Challenge.PhaseVar` and `Stafford38Challenge.WeylAlg` are copied
verbatim from `stafford38-formal/Stafford38/ChallengeDefinitions.lean`; only the
`import`s differ. -/

namespace Stafford

variable {k ι : Type*} [Field k]

/-- The commutator relations presenting a Weyl-type algebra. -/
def freeWeylRelation (omega : Matrix ι ι k)
    (a b : FreeAlgebra k ι) : Prop :=
  ∃ i j,
    a = FreeAlgebra.ι k i * FreeAlgebra.ι k j -
      FreeAlgebra.ι k j * FreeAlgebra.ι k i ∧
    b = algebraMap k (FreeAlgebra k ι) (omega i j)

/-- The free algebra modulo the commutator relations encoded by `omega`. -/
abbrev FreeWeyl (k : Type*) [Field k] (ι : Type*)
    (omega : Matrix ι ι k) := RingQuot (freeWeylRelation omega)

end Stafford

namespace Stafford38Challenge

/-- Index type of the coordinate and momentum generators. -/
abbrev PhaseVar (n : ℕ) := Fin n ⊕ Fin n

/-- The standard presented Weyl algebra, shared with the substantive proof. -/
abbrev WeylAlg (k : Type*) [Field k] (n : ℕ) :=
  Stafford.FreeWeyl k (PhaseVar n) (Matrix.J (Fin n) k)

end Stafford38Challenge

namespace GeneralizedStaffordChallenge

/-- **Two generators, right ideals of the Weyl algebra.** For every field `k` of
characteristic zero and every `n`, every right ideal `I` of `Aₙ(k)` is generated
by two elements: `I = a Aₙ(k) + b Aₙ(k)`. -/
def WeylTwoGeneratedRightStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ)
    (I : Submodule (Stafford38Challenge.WeylAlg k n)ᵐᵒᵖ (Stafford38Challenge.WeylAlg k n)),
    ∃ a b : Stafford38Challenge.WeylAlg k n,
      I = Submodule.span (Stafford38Challenge.WeylAlg k n)ᵐᵒᵖ {a, b}

/-- **Two generators, left ideals of the Weyl algebra.** For every field `k` of
characteristic zero and every `n`, every left ideal `I` of `Aₙ(k)` is generated
by two elements: `I = Aₙ(k) a + Aₙ(k) b`. -/
def WeylTwoGeneratedLeftStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ)
    (I : Submodule (Stafford38Challenge.WeylAlg k n) (Stafford38Challenge.WeylAlg k n)),
    ∃ a b : Stafford38Challenge.WeylAlg k n,
      I = Submodule.span (Stafford38Challenge.WeylAlg k n) {a, b}

end GeneralizedStaffordChallenge

namespace GeneralizedStaffordChallenge

/-- Two generators for right ideals of the Weyl algebra, from
`GeneralizedStafford.Weyl.twoGeneratedRight`. -/
theorem weylTwoGeneratedRight_proof : WeylTwoGeneratedRightStatement.{u} := by
  intro k _ _ n I
  exact GeneralizedStafford.Weyl.twoGeneratedRight k n I

/-- Two generators for left ideals of the Weyl algebra, from
`GeneralizedStafford.Weyl.twoGeneratedLeft`. -/
theorem weylTwoGeneratedLeft_proof : WeylTwoGeneratedLeftStatement.{u} := by
  intro k _ _ n I
  exact GeneralizedStafford.Weyl.twoGeneratedLeft k n I

end GeneralizedStaffordChallenge
