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
`Stafford38Challenge.PhaseVar`, `Stafford38Challenge.WeylAlg`,
`Stafford.Reduction.Stafford38`, `Stafford38Challenge.UniversalStatement` and
`Stafford38.TorsionCyclicity.IsRightTorsion` are copied verbatim from
`stafford38-formal/Stafford38/ChallengeDefinitions.lean`; only the `import`s differ.

The left summand of `PhaseVar n` indexes `x_i`, the right summand `∂_i`; the
relations `ι i ι j − ι j ι i = J i j` with `Matrix.J = [[0, −1], [1, 0]]` give
`[∂_i, x_j] = δ_ij`, all other generators commuting. -/

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

namespace Stafford
namespace Reduction

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- Stafford 3.8 for one element, in written operator order. -/
def Stafford38 (e : A) : Prop := ∃ F R S : A, (1 : A) = e * R + F * e * S

end Reduction
end Stafford

namespace Stafford38Challenge

/-- Stafford's Conjecture 3.8 in its intended nonzero form. -/
def UniversalStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ) (d : WeylAlg k n),
    d ≠ 0 → Stafford.Reduction.Stafford38 d

end Stafford38Challenge

namespace Stafford38.TorsionCyclicity

/-- Every element of a right module is killed by some nonzero right scalar. -/
def IsRightTorsion {A : Type u} {M : Type v} [Ring A]
    [AddCommGroup M] [Module Aᵐᵒᵖ M] : Prop :=
  ∀ m : M, ∃ d : A, d ≠ 0 ∧ (MulOpposite.op d : Aᵐᵒᵖ) • m = 0

end Stafford38.TorsionCyclicity

/-! ## New statements -/

namespace GeneralizedStaffordWeylChallenge

open MulOpposite Stafford38Challenge

/-- Every element of a left module is killed by some nonzero left scalar. -/
def IsLeftTorsion {A : Type u} {M : Type v} [Ring A]
    [AddCommGroup M] [Module A M] : Prop :=
  ∀ m : M, ∃ d : A, d ≠ 0 ∧ d • m = 0

/-! ### Stafford's Conjecture 3.8 and the affine form (Theorem A, Corollary B) -/

/-- **Stafford's Conjecture 3.8** (Stafford 1978, p. 438): for `d ≠ 0` in
`Aₙ(k)` there are `F, R, S` with `1 = d R + F d S`. This is literally the
registered `Stafford38Challenge.UniversalStatement`; here it is the case
`a = 1`, `B = 0` of the affine form (`F = H`). -/
def Conjecture38Statement : Prop := UniversalStatement.{u}

/-- **Affine form (Theorem A for `Aₙ(k)`).** For every nonzero `d`, every
nonzero `a` and every `B` in `Aₙ(k)` there are `H, U, V` with
`1 = d U + (B + H a) d V`. -/
def AffineFormStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ) (d a B : WeylAlg k n),
    d ≠ 0 → a ≠ 0 → ∃ H U V : WeylAlg k n, 1 = d * U + (B + H * a) * d * V

/-- **Fixed-ideal form (Theorem A' for `Aₙ(k)`).** For every nonzero right
ideal `I` of `Aₙ(k)`, every `x` and every nonzero `t` there is `H` with
`I + (x + H t) Aₙ = Aₙ`. -/
def FixedIdealStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ)
    (I : Submodule (WeylAlg k n)ᵐᵒᵖ (WeylAlg k n)), I ≠ ⊥ →
    ∀ x t : WeylAlg k n, t ≠ 0 →
      ∃ H : WeylAlg k n, I ⊔ Submodule.span (WeylAlg k n)ᵐᵒᵖ {x + H * t} = ⊤

/-! ### Torsion modules are cyclic (Corollary C.1), right and left -/

/-- **Torsion cyclicity, right modules.** Every finitely generated torsion
right `Aₙ(k)`-module is cyclic. Same proposition as the registered
`Stafford38CorollaryChallenge.torsionCyclicStatement` of `stafford38-formal`. -/
def TorsionCyclicRightStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ)
    (M : Type v) [AddCommGroup M] [Module (WeylAlg k n)ᵐᵒᵖ M]
    [Module.Finite (WeylAlg k n)ᵐᵒᵖ M],
    Stafford38.TorsionCyclicity.IsRightTorsion (A := WeylAlg k n) (M := M) →
      ∃ z : M, Submodule.span (WeylAlg k n)ᵐᵒᵖ ({z} : Set M) = ⊤

/-- **Torsion cyclicity, left modules.** Every finitely generated torsion
left `Aₙ(k)`-module is cyclic. -/
def TorsionCyclicLeftStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ)
    (M : Type v) [AddCommGroup M] [Module (WeylAlg k n) M]
    [Module.Finite (WeylAlg k n) M],
    IsLeftTorsion (A := WeylAlg k n) (M := M) →
      ∃ z : M, Submodule.span (WeylAlg k n) ({z} : Set M) = ⊤

/-- **Prescribed cyclic generator, right modules (C.1).** In a finitely
generated torsion right `Aₙ(k)`-module `M`, for every `x ∈ M` and every
nonzero `t` there is `h ∈ M` with `M = (x + h t) Aₙ`. -/
def PrescribedCyclicRightStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ)
    (M : Type v) [AddCommGroup M] [Module (WeylAlg k n)ᵐᵒᵖ M]
    [Module.Finite (WeylAlg k n)ᵐᵒᵖ M],
    Stafford38.TorsionCyclicity.IsRightTorsion (A := WeylAlg k n) (M := M) →
    ∀ (x : M) (t : WeylAlg k n), t ≠ 0 →
      ∃ h : M, Submodule.span (WeylAlg k n)ᵐᵒᵖ ({x + op t • h} : Set M) = ⊤

/-- **Prescribed cyclic generator, left modules (C.1 via `Aₙ ≅ Aₙᵒᵖ`).** In a
finitely generated torsion left `Aₙ(k)`-module `M`, for every `x ∈ M` and
every nonzero `t` there is `h ∈ M` with `M = Aₙ (x + t h)`. -/
def PrescribedCyclicLeftStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ)
    (M : Type v) [AddCommGroup M] [Module (WeylAlg k n) M]
    [Module.Finite (WeylAlg k n) M],
    IsLeftTorsion (A := WeylAlg k n) (M := M) →
    ∀ (x : M) (t : WeylAlg k n), t ≠ 0 →
      ∃ h : M, Submodule.span (WeylAlg k n) ({x + t • h} : Set M) = ⊤

/-! ### One-sided ideals are two-generated (Corollary C.2), right and left -/

/-- **Prescribed first generator, right ideals (C.2).** If `a` is a nonzero
element of a right ideal `I` of `Aₙ(k)`, then for every `y ∈ I` and every
nonzero `t` there is `h ∈ I` with `I = a Aₙ + (y + h t) Aₙ`. (Since `Aₙ(k)` is a
domain, any nonzero `a ∈ I` may serve as the first generator.) -/
def PrescribedTwoGeneratedRightStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ)
    (I : Submodule (WeylAlg k n)ᵐᵒᵖ (WeylAlg k n)) (a : WeylAlg k n),
    a ∈ I → a ≠ 0 → ∀ y ∈ I, ∀ t : WeylAlg k n, t ≠ 0 →
      ∃ h ∈ I, I = Submodule.span (WeylAlg k n)ᵐᵒᵖ {a} ⊔
        Submodule.span (WeylAlg k n)ᵐᵒᵖ {y + h * t}

/-- **Prescribed first generator, left ideals.** If `a` is a nonzero element
of a left ideal `I` of `Aₙ(k)`, then for every `y ∈ I` and every nonzero `t`
there is `h ∈ I` with `I = Aₙ a + Aₙ (y + t h)`. -/
def PrescribedTwoGeneratedLeftStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ)
    (I : Submodule (WeylAlg k n) (WeylAlg k n)) (a : WeylAlg k n),
    a ∈ I → a ≠ 0 → ∀ y ∈ I, ∀ t : WeylAlg k n, t ≠ 0 →
      ∃ h ∈ I, I = Submodule.span (WeylAlg k n) {a} ⊔
        Submodule.span (WeylAlg k n) {y + t * h}

end GeneralizedStaffordWeylChallenge

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

/-- Stafford's Conjecture 3.8 for `Aₙ(k)`: for every nonzero `d` there are `F, R, S` with `1 = d R + F d S`. Proved by `GeneralizedStafford.Weyl`. -/
theorem weylConjecture38_proof : GeneralizedStaffordWeylChallenge.Conjecture38Statement.{u} := by
  intro k _ _ n d hd
  exact GeneralizedStafford.Weyl.conjecture38 k n d hd

/-- Theorem A for `Aₙ(k)`, affine form: `1 = d U + (B + H a) d V` for nonzero `d` and `a`. Proved by `GeneralizedStafford.Weyl`. -/
theorem weylAffineForm_proof : GeneralizedStaffordWeylChallenge.AffineFormStatement.{u} := by
  intro k _ _ n d a B hd ha
  exact GeneralizedStafford.Weyl.affineForm k n d a B hd ha

/-- Theorem A' for `Aₙ(k)`: a nonzero right ideal `I` satisfies `I + (x + H t) Aₙ(k) = Aₙ(k)`. Proved by `GeneralizedStafford.Weyl`. -/
theorem weylFixedIdeal_proof : GeneralizedStaffordWeylChallenge.FixedIdealStatement.{u} := by
  intro k _ _ n I hI x t ht
  exact GeneralizedStafford.Weyl.fixedIdealForm k n I hI x t ht

/-- Corollary C.1: a finitely generated torsion right `Aₙ(k)`-module is cyclic. Proved by `GeneralizedStafford.Weyl`. -/
theorem weylTorsionCyclicRight_proof : GeneralizedStaffordWeylChallenge.TorsionCyclicRightStatement.{u, v} := by
  intro k _ _ n M i1 i2 i3 hM
  exact @GeneralizedStafford.Weyl.torsionCyclicRight k _ _ n M i1 i2 i3 hM

/-- Corollary C.1: a finitely generated torsion left `Aₙ(k)`-module is cyclic. Proved by `GeneralizedStafford.Weyl`. -/
theorem weylTorsionCyclicLeft_proof : GeneralizedStaffordWeylChallenge.TorsionCyclicLeftStatement.{u, v} := by
  intro k _ _ n M i1 i2 i3 hM
  exact @GeneralizedStafford.Weyl.torsionCyclicLeft k _ _ n M i1 i2 i3 hM

/-- Corollary C.1, prescribed generator, right modules: `M = (x + h t) Aₙ(k)`. Proved by `GeneralizedStafford.Weyl`. -/
theorem weylPrescribedCyclicRight_proof : GeneralizedStaffordWeylChallenge.PrescribedCyclicRightStatement.{u, v} := by
  intro k _ _ n M i1 i2 i3 hM x t ht
  exact @GeneralizedStafford.Weyl.prescribedCyclicRight k _ _ n M i1 i2 i3 hM x t ht

/-- Corollary C.1, prescribed generator, left modules: `M = Aₙ(k) (x + t h)`. Proved by `GeneralizedStafford.Weyl`. -/
theorem weylPrescribedCyclicLeft_proof : GeneralizedStaffordWeylChallenge.PrescribedCyclicLeftStatement.{u, v} := by
  intro k _ _ n M i1 i2 i3 hM x t ht
  exact @GeneralizedStafford.Weyl.prescribedCyclicLeft k _ _ n M i1 i2 i3 hM x t ht

/-- Corollary C.2, prescribed first generator, right ideals: `I = a Aₙ(k) + (y + h t) Aₙ(k)`. Proved by `GeneralizedStafford.Weyl`. -/
theorem weylPrescribedTwoGeneratedRight_proof : GeneralizedStaffordWeylChallenge.PrescribedTwoGeneratedRightStatement.{u} := by
  intro k _ _ n I a haI ha y hy t ht
  exact GeneralizedStafford.Weyl.prescribedTwoGeneratedRight k n I a haI ha y hy t ht

/-- Corollary C.2, prescribed first generator, left ideals: `I = Aₙ(k) a + Aₙ(k) (y + t h)`. Proved by `GeneralizedStafford.Weyl`. -/
theorem weylPrescribedTwoGeneratedLeft_proof : GeneralizedStaffordWeylChallenge.PrescribedTwoGeneratedLeftStatement.{u} := by
  intro k _ _ n I a haI ha y hy t ht
  exact GeneralizedStafford.Weyl.prescribedTwoGeneratedLeft k n I a haI ha y hy t ht

end GeneralizedStaffordChallenge
