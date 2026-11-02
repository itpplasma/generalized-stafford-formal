import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.FreeAlgebra
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.Module.LinearMap.End

/-!
# Affine generation over simple Noetherian rings with infinite centre

This file states Theorem A', Theorem A and Corollaries B and C (C.1 and C.2),
and their applications to the Weyl algebra, filtered rings, simple quotients
of enveloping algebras and rings of differential operators.
It imports only Mathlib and defines everything else inline.

## Conventions

* Rings are associative and unital; `R` is nonzero because Mathlib's
  `IsSimpleRing` includes nontriviality.
* Modules are **right** modules. A right `R`-module `M` is a Mathlib module
  over the opposite ring, `[Module Rᵐᵒᵖ M]`; the product `m r` is written
  `MulOpposite.op r • m`. In particular a right ideal of `R` is a
  `Submodule Rᵐᵒᵖ R`, and `Submodule.span Rᵐᵒᵖ {x}` is the principal right
  ideal `xR` (its elements are the products `x * r`, in this order). The
  quotient `R ⧸ I` is the cyclic right module `R/I`.
* Products in `R` are read in the displayed order: `(B + H * a) * d * V`
  is `(B + H a) d V`, never a reordering of it.
* `IsRegularElement d` is two-sided regularity: `d x = 0 → x = 0` and
  `x d = 0 → x = 0`. It is literally Mathlib's membership `d ∈ R⁰`
  (`mem_nonZeroDivisors_iff` holds by `Iff.rfl`); it is spelled out here so
  that a reader need not look up the sidedness of `nonZeroDivisors`.
* `DevDimLE R M n` is the right **Gabriel--Rentschler (deviation)
  dimension** bound `Kdim M ≤ n` (written `Kdim`; it is
  unrelated to Mathlib's `Order.KrullDimLE` and `Ring.KrullDimLE`), defined
  on the lattice of right submodules: `Kdim ≤ 0` means that every descending chain stabilizes, and
  `Kdim ≤ n + 1` means that for every descending chain
  `M₀ ≥ M₁ ≥ ⋯` all but finitely many factors `Mᵢ/Mᵢ₊₁` have `Kdim ≤ n`.
  The factor `Mᵢ/Mᵢ₊₁` is represented by the interval `[Mᵢ₊₁, Mᵢ]` of the
  submodule lattice, which is order isomorphic to its submodule lattice.
  The zero module satisfies every bound, so "`Kdim M` is a finite integer
  `≥ -1`" is `∃ n : ℕ, DevDimLE R M n` (`HasFiniteDevDim`).
  This is **not** the classical (Krull) dimension of chains of prime ideals
  and not Mathlib's `ringKrullDim`/`Module.length`; it is the deviation of
  the submodule poset. `DevDimLEOmega R M` is `Kdim M ≤ ω`: for every
  descending chain all but finitely many factors have finite dimension.
* `IsGoldieTorsion R M`: every `m` has `m s = 0` for some regular `s`.
* (S) is Mathlib's `IsSimpleRing R` (nonzero, only the trivial two-sided
  ideals). (N) is `IsNoetherian Rᵐᵒᵖ R`: right ideals satisfy the ascending
  chain condition. (Z) is `Infinite (Subring.center R)`: the centre is
  infinite. Under (S) the centre is a field (Mathlib's
  `IsSimpleRing.isField_center`), so (Z) is the same as "`R` is an algebra
  over an infinite central field".
* Finitely generated right modules are `[Module.Finite Rᵐᵒᵖ M]`.

Rings live in universe `u` and modules in universe `v`; the theorems are
stated for all universes. The compared theorems are the `theorem`s below;
each `sorry` is a deliberate hole. The proofs are in
`GeneralizedStaffordSolution.lean` (identical copy `Solution.lean`) of this
repository; holes without a proof there are listed in `docs/open-holes.md`.

Left-handed statements are stated for the Weyl algebra and, through the opposite ring `Rᵐᵒᵖ`, for filtered rings (last section); for the Weyl algebra the left case is the right case transported by the transposition anti-automorphism.
-/

universe u v

namespace GeneralizedStaffordChallenge

open MulOpposite

/-! ## Regular elements, deviation and Goldie torsion -/

section Definitions

variable (R : Type u) [Ring R]

/-- An element `d` of `R` is **regular** if it is a two-sided non-zero-divisor:
`d x = 0` implies `x = 0`, and `x d = 0` implies `x = 0` .
This is definitionally Mathlib's `d ∈ R⁰`. -/
def IsRegularElement {R : Type u} [Ring R] (d : R) : Prop :=
  (∀ x : R, d * x = 0 → x = 0) ∧ (∀ x : R, x * d = 0 → x = 0)

/-- Finite Gabriel--Rentschler deviation of a partial order. `PosetDevLE 0 α`
says that every descending chain in `α` stabilizes; `PosetDevLE (n + 1) α`
says that for every descending chain `c₀ ≥ c₁ ≥ ⋯` all but finitely many
closed intervals `[cᵢ₊₁, cᵢ]` satisfy `PosetDevLE n`, i.e. all but finitely
many factors have deviation `< n + 1` . -/
def PosetDevLE : (n : ℕ) → (α : Type v) → [PartialOrder α] → Prop
  | 0, α, _ => ∀ c : ℕ → α, Antitone c → ∃ N, ∀ i, N ≤ i → c i = c N
  | n + 1, α, _ => ∀ c : ℕ → α, Antitone c →
      ∃ N, ∀ i, N ≤ i → PosetDevLE n (Set.Icc (c (i + 1)) (c i))

variable (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- `DevDimLE R M n`: `Kdim M ≤ n` (written `Kdim`;
Gabriel--Rentschler deviation, not classical Krull dimension). The right
module `M` has right deviation dimension at most `n` , defined
on the lattice of right submodules of `M`. -/
def DevDimLE (n : ℕ) : Prop :=
  PosetDevLE n (Submodule Rᵐᵒᵖ M)

/-- `Kdim M` is a finite integer (possibly `-1`, which happens exactly when
`M = 0`). -/
def HasFiniteDevDim : Prop :=
  ∃ n : ℕ, DevDimLE R M n

/-- `DevDimLEOmega R M`: `Kdim M ≤ ω`, that is, for every descending chain of
right submodules `M₀ ≥ M₁ ≥ ⋯` all but finitely many factors `Mᵢ/Mᵢ₊₁`
(the intervals `[Mᵢ₊₁, Mᵢ]`) have finite deviation. -/
def DevDimLEOmega : Prop :=
  ∀ c : ℕ → Submodule Rᵐᵒᵖ M, Antitone c → ∃ N, ∀ i, N ≤ i →
    ∃ n : ℕ, PosetDevLE n (Set.Icc (c (i + 1)) (c i))

/-- `M` is **Goldie-torsion**: every `m ∈ M` satisfies
`m s = 0` for some regular `s ∈ R`. -/
def IsGoldieTorsion : Prop :=
  ∀ m : M, ∃ s : R, IsRegularElement s ∧ op s • m = 0

/-- Hypothesis (H_all): `δ(d) = Kdim(R/dR)` is a finite integer for every
regular `d`. -/
def HAll : Prop :=
  ∀ d : R, IsRegularElement d → HasFiniteDevDim R (R ⧸ Submodule.span Rᵐᵒᵖ {d})

/-- Hypothesis (H_omega): `Kdim R ≤ ω` for the right regular module `R_R`. -/
def HOmega : Prop :=
  DevDimLEOmega R R

end Definitions

/-! ## Theorem A' and Theorem A -/

/-- **Theorem A' (fixed ideal).** Let `R` be a simple (S), right Noetherian (N)
ring with infinite centre (Z). Let `I` be a right ideal containing a regular
element such that `Kdim(R/I)` is a finite integer. Then for
every `x ∈ R` and every nonzero `t ∈ R` there is `H ∈ R` with
`I + (x + H t)R = R`. -/
def FixedIdealStatement : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    [Infinite (Subring.center R)] (I : Submodule Rᵐᵒᵖ R),
    (∃ s ∈ I, IsRegularElement s) → HasFiniteDevDim R (R ⧸ I) →
    ∀ x t : R, t ≠ 0 →
      ∃ H : R, I ⊔ Submodule.span Rᵐᵒᵖ {x + H * t} = ⊤

/-- **Theorem A (fixed anchor).** Let `R` satisfy (S), (N), (Z) and let `d` be a
regular element with `δ(d) = Kdim(R/dR)` a finite integer. For every nonzero
`a ∈ R` (possibly a zero-divisor) and every `B ∈ R` there are `H, U, V ∈ R`
with `1 = d U + (B + H a) d V`. -/
def FixedAnchorStatement : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    [Infinite (Subring.center R)] (d : R),
    IsRegularElement d → HasFiniteDevDim R (R ⧸ Submodule.span Rᵐᵒᵖ {d}) →
    ∀ a B : R, a ≠ 0 →
      ∃ H U V : R, 1 = d * U + (B + H * a) * d * V

/-- Theorem A' (fixed ideal). -/
theorem fixedIdeal : FixedIdealStatement.{u} := by
  sorry

/-- Theorem A (fixed anchor). -/
theorem fixedAnchor : FixedAnchorStatement.{u} := by
  sorry

/-! ## Corollary B -/

/-- **Corollary B, fixed anchor.** Let `R` satisfy (S), (N), (Z) and
`Kdim R ≤ ω`. For every regular `d`, every nonzero `a` and every `B` there are
`H, U, V` with `1 = d U + (B + H a) d V`. -/
def CorollaryBFixedAnchorStatement : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    [Infinite (Subring.center R)], HOmega R →
    ∀ d a B : R, IsRegularElement d → a ≠ 0 →
      ∃ H U V : R, 1 = d * U + (B + H * a) * d * V

/-- **Corollary B, fixed ideal.** Let `R` satisfy (S), (N), (Z) and
`Kdim R ≤ ω`. For every right ideal `I` containing a regular element, every
`x` and every nonzero `t` there is `H` with `I + (x + H t)R = R`. -/
def CorollaryBFixedIdealStatement : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    [Infinite (Subring.center R)], HOmega R →
    ∀ I : Submodule Rᵐᵒᵖ R, (∃ s ∈ I, IsRegularElement s) →
    ∀ x t : R, t ≠ 0 →
      ∃ H : R, I ⊔ Submodule.span Rᵐᵒᵖ {x + H * t} = ⊤

/-- Corollary B for Theorem A. -/
theorem corollaryB_fixedAnchor : CorollaryBFixedAnchorStatement.{u} := by
  sorry

/-- Corollary B for Theorem A'. -/
theorem corollaryB_fixedIdeal : CorollaryBFixedIdealStatement.{u} := by
  sorry

/-! ## Corollary C.1 -/

/-- **Corollary C.1 (prescribed cyclic generator).** Let `R` satisfy (S), (N),
(Z) and let `M` be a finitely generated Goldie-torsion right module with
`Kdim M` a finite integer. For every `x ∈ M` and every nonzero `t ∈ R` there
is `h ∈ M` with `M = (x + h t)R`. -/
def CorollaryC1Statement : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    [Infinite (Subring.center R)]
    (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M],
    IsGoldieTorsion R M → HasFiniteDevDim R M →
    ∀ (x : M) (t : R), t ≠ 0 →
      ∃ h : M, Submodule.span Rᵐᵒᵖ {x + op t • h} = ⊤

/-- **Corollary C.1 under (H_all).** Let `R` satisfy (S), (N), (Z) and (H_all).
Every finitely generated Goldie-torsion right module `M` satisfies: for every
`x ∈ M` and nonzero `t ∈ R` there is `h ∈ M` with `M = (x + h t)R`. -/
def CorollaryC1HAllStatement : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    [Infinite (Subring.center R)], HAll R →
    ∀ (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M],
    IsGoldieTorsion R M →
    ∀ (x : M) (t : R), t ≠ 0 →
      ∃ h : M, Submodule.span Rᵐᵒᵖ {x + op t • h} = ⊤

/-- **Corollary C.1 under `Kdim R ≤ ω`.** Let `R` satisfy (S), (N), (Z) and
(H_omega). Every finitely generated Goldie-torsion right module `M` satisfies:
for every `x ∈ M` and nonzero `t ∈ R` there is `h ∈ M` with `M = (x + h t)R`. -/
def CorollaryC1OmegaStatement : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    [Infinite (Subring.center R)], HOmega R →
    ∀ (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M],
    IsGoldieTorsion R M →
    ∀ (x : M) (t : R), t ≠ 0 →
      ∃ h : M, Submodule.span Rᵐᵒᵖ {x + op t • h} = ⊤

/-- **Corollary C.1, stable cyclicity.** Let `R` satisfy (S), (N), (Z), let `c, u`
be Goldie-torsion elements of a right module `M` (each is killed by a regular
element) with `Kdim(uR)` a finite integer.
For every nonzero `t ∈ R` there is `H ∈ R` with `cR + uR = (c + u H t)R`. -/
def CorollaryC1StableStatement : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    [Infinite (Subring.center R)]
    (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] (c u : M),
    (∃ s : R, IsRegularElement s ∧ op s • c = 0) →
    (∃ s : R, IsRegularElement s ∧ op s • u = 0) →
    HasFiniteDevDim R (Submodule.span Rᵐᵒᵖ {u}) →
    ∀ t : R, t ≠ 0 →
      ∃ H : R, Submodule.span Rᵐᵒᵖ {c, u} = Submodule.span Rᵐᵒᵖ {c + op (H * t) • u}

/-- Corollary C.1 (finite dimension hypothesis). -/
theorem corollaryC1 : CorollaryC1Statement.{u, v} := by
  sorry

/-- Corollary C.1 under (H_all). -/
theorem corollaryC1_hAll : CorollaryC1HAllStatement.{u, v} := by
  sorry

/-- Corollary C.1 under (H_omega). -/
theorem corollaryC1_omega : CorollaryC1OmegaStatement.{u, v} := by
  sorry

/-- Corollary C.1, stable cyclicity. -/
theorem corollaryC1_stable : CorollaryC1StableStatement.{u, v} := by
  sorry

/-! ## Corollary C.2

The condition `aQ = IQ` (with `Q` the classical right quotient ring)
is stated elementwise: `a ∈ I` and every `y ∈ I` has a regular `s` with
`y s ∈ aR`. Under (S), (N) these are equivalent: `aQ ⊆ IQ` because `a ∈ I`,
and `y ∈ aQ` iff `y = a r s⁻¹` iff `y s = a r` for some `r` and regular `s`. -/

/-- **Existence of a full-rank element** (first step of Corollary C.2). Let `R`
satisfy (S) and (N). Every right ideal `I` contains an `a` with `aQ = IQ`, that
is, every `y ∈ I` has a regular `s` with `y s ∈ aR`. Corollary C.2 is stated
under (S), (N), (Z), (H_all); this step needs only (S) and (N) (Goldie's
theorem), so the statement here has fewer hypotheses and is still true. -/
def CorollaryC2FullRankStatement : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    (I : Submodule Rᵐᵒᵖ R),
    ∃ a ∈ I, ∀ y ∈ I,
      ∃ s : R, IsRegularElement s ∧ y * s ∈ Submodule.span Rᵐᵒᵖ {a}

/-- **Corollary C.2, prescribed form.** Let `R` satisfy (S), (N), (Z) and
(H_all), and let `I` be a right ideal. If `a ∈ I` satisfies `aQ = IQ` (every
`y ∈ I` has a regular `s` with `y s ∈ aR`), then for every `y ∈ I` and every
nonzero `t ∈ R` there is `h ∈ I` with `I = aR + (y + h t)R`. -/
def CorollaryC2PrescribedStatement : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    [Infinite (Subring.center R)], HAll R →
    ∀ (I : Submodule Rᵐᵒᵖ R) (a : R), a ∈ I →
    (∀ y ∈ I, ∃ s : R, IsRegularElement s ∧ y * s ∈ Submodule.span Rᵐᵒᵖ {a}) →
    ∀ y ∈ I, ∀ t : R, t ≠ 0 →
      ∃ h ∈ I, I = Submodule.span Rᵐᵒᵖ {a} ⊔ Submodule.span Rᵐᵒᵖ {y + h * t}

/-- **Corollary C.2 (two generators).** Let `R` satisfy (S), (N), (Z) and
(H_all). Every right ideal `I` of `R` is generated by two elements:
`I = aR + bR` for some `a, b ∈ R`. -/
def CorollaryC2Statement : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    [Infinite (Subring.center R)], HAll R →
    ∀ I : Submodule Rᵐᵒᵖ R, ∃ a b : R, I = Submodule.span Rᵐᵒᵖ {a, b}

/-- **Corollary C.2 under `Kdim R ≤ ω`.** Let `R` satisfy (S), (N), (Z) and
(H_omega). Every right ideal `I` of `R` is generated by two elements:
`I = aR + bR` for some `a, b ∈ R`. -/
def CorollaryC2OmegaStatement : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    [Infinite (Subring.center R)], HOmega R →
    ∀ I : Submodule Rᵐᵒᵖ R, ∃ a b : R, I = Submodule.span Rᵐᵒᵖ {a, b}

/-- Existence of `a ∈ I` with `aQ = IQ` (first step of Corollary C.2). -/
theorem corollaryC2_fullRank : CorollaryC2FullRankStatement.{u} := by
  sorry

/-- Corollary C.2, prescribed form. -/
theorem corollaryC2_prescribed : CorollaryC2PrescribedStatement.{u} := by
  sorry

/-- Corollary C.2, every right ideal is two-generated. -/
theorem corollaryC2 : CorollaryC2Statement.{u} := by
  sorry

/-- Corollary C.2 under (H_omega). -/
theorem corollaryC2_omega : CorollaryC2OmegaStatement.{u} := by
  sorry

end GeneralizedStaffordChallenge

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

/-- Two generators for right ideals of the Weyl algebra `Aₙ(k)`. -/
theorem weylTwoGeneratedRight : WeylTwoGeneratedRightStatement.{u} := by
  sorry

/-- Two generators for left ideals of the Weyl algebra `Aₙ(k)`. -/
theorem weylTwoGeneratedLeft : WeylTwoGeneratedLeftStatement.{u} := by
  sorry

/-- Stafford's Conjecture 3.8 for `Aₙ(k)`: for every nonzero `d` there are `F, R, S` with `1 = d R + F d S`. -/
theorem weylConjecture38 : GeneralizedStaffordWeylChallenge.Conjecture38Statement.{u} := by
  sorry

/-- Theorem A for `Aₙ(k)`, affine form: `1 = d U + (B + H a) d V` for nonzero `d` and `a`. -/
theorem weylAffineForm : GeneralizedStaffordWeylChallenge.AffineFormStatement.{u} := by
  sorry

/-- Theorem A' for `Aₙ(k)`: a nonzero right ideal `I` satisfies `I + (x + H t) Aₙ(k) = Aₙ(k)`. -/
theorem weylFixedIdeal : GeneralizedStaffordWeylChallenge.FixedIdealStatement.{u} := by
  sorry

/-- Corollary C.1: a finitely generated torsion right `Aₙ(k)`-module is cyclic. -/
theorem weylTorsionCyclicRight : GeneralizedStaffordWeylChallenge.TorsionCyclicRightStatement.{u, v} := by
  sorry

/-- Corollary C.1: a finitely generated torsion left `Aₙ(k)`-module is cyclic. -/
theorem weylTorsionCyclicLeft : GeneralizedStaffordWeylChallenge.TorsionCyclicLeftStatement.{u, v} := by
  sorry

/-- Corollary C.1, prescribed generator, right modules: `M = (x + h t) Aₙ(k)`. -/
theorem weylPrescribedCyclicRight : GeneralizedStaffordWeylChallenge.PrescribedCyclicRightStatement.{u, v} := by
  sorry

/-- Corollary C.1, prescribed generator, left modules: `M = Aₙ(k) (x + t h)`. -/
theorem weylPrescribedCyclicLeft : GeneralizedStaffordWeylChallenge.PrescribedCyclicLeftStatement.{u, v} := by
  sorry

/-- Corollary C.2, prescribed first generator, right ideals: `I = a Aₙ(k) + (y + h t) Aₙ(k)`. -/
theorem weylPrescribedTwoGeneratedRight : GeneralizedStaffordWeylChallenge.PrescribedTwoGeneratedRightStatement.{u} := by
  sorry

/-- Corollary C.2, prescribed first generator, left ideals: `I = Aₙ(k) a + Aₙ(k) (y + t h)`. -/
theorem weylPrescribedTwoGeneratedLeft : GeneralizedStaffordWeylChallenge.PrescribedTwoGeneratedLeftStatement.{u} := by
  sorry

end GeneralizedStaffordChallenge

/-! ## Filtered rings

The hypothesis "`gr R` is commutative Noetherian of finite Krull dimension" is
stated through an identification of `gr R = ⨁ₙ Fₙ/Fₙ₋₁` with a commutative
graded `k`-algebra `G = ⨁ₙ 𝒜ₙ` (`GradedAlgebra 𝒜`): surjective `k`-linear
symbol maps `grₙ : Fₙ → 𝒜ₙ` with kernel `Fₙ₋₁` (`F₋₁ = 0`) that multiply,
`gr_{i+j}(x y) = grᵢ(x) grⱼ(y)`.

*Equivalence with the classical hypothesis.* If `gr R` (with its usual
multiplication of classes) is commutative, take `G = gr R`, `𝒜ₙ = Fₙ/Fₙ₋₁`
and `grₙ` the quotient maps. Conversely, the maps `grₙ` induce `k`-linear
isomorphisms `Fₙ/Fₙ₋₁ ≅ 𝒜ₙ` which carry the product of classes to the
product of `G` (`gr_mul`); since `G` is the internal direct sum of the `𝒜ₙ`,
their sum is a graded ring isomorphism `gr R ≅ G`. Being Noetherian and the
Krull dimension (`ringKrullDim`, chains of prime ideals) are invariant under
ring isomorphism. So the existential hypothesis below holds iff `gr R` is
commutative Noetherian of Krull dimension `≤ m`. The ring `G` is taken in the
universe of `R`, where `gr R` lives. Multiplicativity of the filtration is stated elementwise. -/

namespace GeneralizedStaffordChallenge

open MulOpposite

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

/-- Filtered rings: (N), (Z), `Kdim ≤ m` on both sides. -/
theorem filteredHypotheses : FilteredHypothesesStatement.{u} := by
  sorry

/-- Filtered rings: Theorem A, both forms (right and left). -/
theorem filteredTheoremA : FilteredTheoremAStatement.{u} := by
  sorry

/-- Filtered rings: Theorem A' on both sides. -/
theorem filteredFixedIdeal : FilteredFixedIdealStatement.{u} := by
  sorry

/-- Filtered rings: Corollary C.1 on both sides. -/
theorem filteredPrescribedCyclic : FilteredPrescribedCyclicStatement.{u, v} := by
  sorry

/-- Filtered rings: Corollary C.2 on both sides. -/
theorem filteredTwoGenerated : FilteredTwoGeneratedStatement.{u} := by
  sorry

/-- Filtered rings with a domain as associated graded ring: Theorem A for every
nonzero anchor, on both sides. -/
theorem filteredDomain : FilteredDomainStatement.{u} := by
  sorry

/-! ## Simple quotients of enveloping algebras

A simple quotient `U(𝔤)/J` of the universal enveloping algebra of a
finite-dimensional Lie algebra `𝔤` over an infinite field `k` is a simple
`k`-algebra `R` with a surjective `k`-algebra map `f : U(𝔤) → R`: by the first
isomorphism theorem `R ≅ U(𝔤)/ker f`, and conversely the quotient map `U(𝔤) → U(𝔤)/J`
is such a map. The Krull dimension bound is `dim 𝔤`. As for the filtered rings
above, the statements for `R` and for `Rᵐᵒᵖ` are written out on both sides. -/

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

/-- Simple quotients of enveloping algebras: (N), (Z) and `Kdim ≤ dim 𝔤` on both sides. -/
theorem envelopingHypotheses : EnvelopingHypothesesStatement.{u} := by
  sorry

/-- Simple quotients of enveloping algebras: Theorem A, both forms (right and left). -/
theorem envelopingTheoremA : EnvelopingTheoremAStatement.{u} := by
  sorry

/-- Simple quotients of enveloping algebras: Theorem A' on both sides. -/
theorem envelopingFixedIdeal : EnvelopingFixedIdealStatement.{u} := by
  sorry

/-- Simple quotients of enveloping algebras: Corollary C.1 on both sides. -/
theorem envelopingPrescribedCyclic : EnvelopingPrescribedCyclicStatement.{u, v} := by
  sorry

/-- Simple quotients of enveloping algebras: Corollary C.2 on both sides. -/
theorem envelopingTwoGenerated : EnvelopingTwoGeneratedStatement.{u} := by
  sorry

end GeneralizedStaffordChallenge

namespace GlobalStaffordChallenge

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]

/-- Multiplication by `a`, as a `k`-linear endomorphism of `A`. -/
def multiplication (a : A) : Module.End k A := LinearMap.mulLeft k a

/-- The commutator `[P, a] = P ∘ a - a ∘ P` of an endomorphism with a
multiplication operator. -/
def commutator (P : Module.End k A) (a : A) : Module.End k A :=
  P * multiplication (k := k) a - multiplication (k := k) a * P

/-- `IsOrderLE n P` says that `P` is a differential operator of order at most
`n`: order `0` operators commute with every multiplication, and `P` has order
at most `n + 1` when every commutator `[P, a]` has order at most `n`. -/
def IsOrderLE : ℕ → Module.End k A → Prop
  | 0, P => ∀ a : A, commutator P a = 0
  | n + 1, P => ∀ a : A, IsOrderLE n (commutator P a)

/-- A finite-order `k`-linear differential operator on `A`. -/
def IsDifferentialOperator (P : Module.End k A) : Prop :=
  ∃ n : ℕ, IsOrderLE n P

end GlobalStaffordChallenge

/-! ## Differential operators on a smooth affine variety

Let `k` be a field of characteristic zero and `A` a smooth domain of finite type over `k`.
Let `D_k(A)` be the ring of `k`-linear finite-order differential operators on `A`, as defined by
`GlobalStaffordChallenge.IsDifferentialOperator`. Products are compositions. The closure proofs
of `diffOps` below are complete and elementary (`[PQ, a] = P [Q, a] + [P, a] Q`); they are not
compared theorems. The statements that need only elements (Theorem A, the Global Stafford
identity) are written in `Module.End k A` with explicit `IsDifferentialOperator` side
conditions. -/

namespace GeneralizedStaffordChallenge

open GlobalStaffordChallenge

section DiffOps

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]

theorem endCommutator_zero (a : A) :
    GlobalStaffordChallenge.commutator (0 : Module.End k A) a = 0 := by
  simp [GlobalStaffordChallenge.commutator]

theorem endCommutator_add (P Q : Module.End k A) (a : A) :
    GlobalStaffordChallenge.commutator (P + Q) a =
      GlobalStaffordChallenge.commutator P a + GlobalStaffordChallenge.commutator Q a := by
  simp only [GlobalStaffordChallenge.commutator, add_mul, mul_add]; abel

theorem endCommutator_mul (P Q : Module.End k A) (a : A) :
    GlobalStaffordChallenge.commutator (P * Q) a =
      P * GlobalStaffordChallenge.commutator Q a + GlobalStaffordChallenge.commutator P a * Q := by
  simp only [GlobalStaffordChallenge.commutator, mul_sub, sub_mul, mul_assoc]; abel

theorem isOrderLE_zero : ∀ n, IsOrderLE n (0 : Module.End k A)
  | 0 => fun a => endCommutator_zero a
  | n + 1 => fun a => by rw [endCommutator_zero]; exact isOrderLE_zero n

theorem isOrderLE_add : ∀ {n} {P Q : Module.End k A},
    IsOrderLE n P → IsOrderLE n Q → IsOrderLE n (P + Q)
  | 0, _, _, hP, hQ => fun a => by rw [endCommutator_add, hP a, hQ a, add_zero]
  | _ + 1, _, _, hP, hQ => fun a => by
      rw [endCommutator_add]; exact isOrderLE_add (hP a) (hQ a)

theorem isOrderLE_succ : ∀ {n} {P : Module.End k A}, IsOrderLE n P → IsOrderLE (n + 1) P
  | 0, _, hP => fun a => by rw [hP a]; exact isOrderLE_zero 0
  | _ + 1, _, hP => fun a => isOrderLE_succ (hP a)

theorem isOrderLE_mono {m n : ℕ} {P : Module.End k A} (h : m ≤ n) (hP : IsOrderLE m P) :
    IsOrderLE n P := by
  induction n, h using Nat.le_induction with
  | base => exact hP
  | succ n _ ih => exact isOrderLE_succ ih

/-- Orders add under composition. -/
theorem isOrderLE_mul : ∀ (N : ℕ) {m n : ℕ} {P Q : Module.End k A}, m + n = N →
    IsOrderLE m P → IsOrderLE n Q → IsOrderLE N (P * Q)
  | 0, m, n, P, Q, h, hP, hQ => by
      obtain ⟨rfl, rfl⟩ : m = 0 ∧ n = 0 := by omega
      intro a
      rw [endCommutator_mul, hP a, hQ a, mul_zero, zero_mul, add_zero]
  | N + 1, m, n, P, Q, h, hP, hQ => fun a => by
      rw [endCommutator_mul]
      refine isOrderLE_add ?_ ?_
      · match n, hQ with
        | 0, hQ => rw [hQ a, mul_zero]; exact isOrderLE_zero N
        | n + 1, hQ => exact isOrderLE_mul N (by omega) hP (hQ a)
      · match m, hP with
        | 0, hP => rw [hP a, zero_mul]; exact isOrderLE_zero N
        | m + 1, hP => exact isOrderLE_mul N (by omega) (hP a) hQ

end DiffOps

/-- The `k`-subalgebra `D_k(A)` of `Module.End k A`: the finite-order differential operators,
with composition as product. -/
def diffOps (k A : Type u) [CommRing k] [CommRing A] [Algebra k A] :
    Subalgebra k (Module.End k A) where
  carrier := {P | IsDifferentialOperator P}
  add_mem' := fun ⟨m, hP⟩ ⟨n, hQ⟩ =>
    ⟨max m n, isOrderLE_add (isOrderLE_mono (le_max_left m n) hP)
      (isOrderLE_mono (le_max_right m n) hQ)⟩
  mul_mem' := fun ⟨m, hP⟩ ⟨n, hQ⟩ => ⟨m + n, isOrderLE_mul _ rfl hP hQ⟩
  algebraMap_mem' c := ⟨0, fun _ => sub_eq_zero.mpr (Algebra.commutes c _)⟩

end GeneralizedStaffordChallenge

namespace GeneralizedStaffordChallenge

open MulOpposite GlobalStaffordChallenge

/-- Two generators for right ideals of `D_k(A)`. For a field `k` of characteristic zero and a
smooth domain `A` of finite type over `k`, every right ideal `I` of `D_k(A)` is generated by two
elements: `I = a D_k(A) + b D_k(A)`. -/
def DiffOpTwoGeneratedRightStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
    (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.Smooth k A]
    (I : Submodule (diffOps k A)ᵐᵒᵖ (diffOps k A)),
    ∃ a b : diffOps k A, I = Submodule.span (diffOps k A)ᵐᵒᵖ {a, b}

/-- Two generators for left ideals of `D_k(A)`. With `k` and `A` as above, every left ideal `I`
of `D_k(A)` is generated by two elements: `I = D_k(A) a + D_k(A) b`. -/
def DiffOpTwoGeneratedLeftStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
    (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.Smooth k A]
    (I : Submodule (diffOps k A) (diffOps k A)),
    ∃ a b : diffOps k A, I = Submodule.span (diffOps k A) {a, b}

/-- Theorem A for `D_k(A)`. With `k` and `A` as above, for all differential operators `d, a, B`
with `d ≠ 0` and `a ≠ 0` there are differential operators `H, U, V` with
`1 = d U + (B + H a) d V` (right form), and differential operators `H, U, V` with
`1 = U d + V d (B + a H)` (left form). Products are compositions. -/
def DiffOpFixedAnchorStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
    (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.Smooth k A]
    (d a B : Module.End k A),
    IsDifferentialOperator d → IsDifferentialOperator a → IsDifferentialOperator B →
    d ≠ 0 → a ≠ 0 →
      (∃ H U V : Module.End k A,
        IsDifferentialOperator H ∧ IsDifferentialOperator U ∧ IsDifferentialOperator V ∧
        (1 : Module.End k A) = d * U + (B + H * a) * d * V) ∧
      (∃ H U V : Module.End k A,
        IsDifferentialOperator H ∧ IsDifferentialOperator U ∧ IsDifferentialOperator V ∧
        (1 : Module.End k A) = U * d + V * d * (B + a * H))

/-- The Global Stafford identity for `D_k(A)`. With `k` and `A` as above, for every nonzero
differential operator `d` there are differential operators `F, R, S` with `1 = d R + F d S`,
the products being compositions. -/
def DiffOpGlobalStaffordStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
    (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.Smooth k A]
    (d : Module.End k A),
    IsDifferentialOperator d → d ≠ 0 →
      ∃ F R S : Module.End k A,
        IsDifferentialOperator F ∧ IsDifferentialOperator R ∧
        IsDifferentialOperator S ∧
        (1 : Module.End k A) = d * R + F * d * S

/-- Cyclicity of torsion right `D_k(A)`-modules. With `k` and `A` as above, let `M` be a finitely
generated right `D_k(A)`-module in which every element is killed by a nonzero operator. For every
`x ∈ M` and every nonzero `t ∈ D_k(A)` there is `h ∈ M` with `M = (x + h t) D_k(A)`; in
particular `M` is cyclic. -/
def DiffOpCyclicRightStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
    (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.Smooth k A]
    (M : Type v) [AddCommGroup M] [Module (diffOps k A)ᵐᵒᵖ M]
    [Module.Finite (diffOps k A)ᵐᵒᵖ M],
    (∀ m : M, ∃ s : diffOps k A, s ≠ 0 ∧ op s • m = 0) →
    ∀ (x : M) (t : diffOps k A), t ≠ 0 →
      ∃ h : M, Submodule.span (diffOps k A)ᵐᵒᵖ {x + op t • h} = ⊤

/-- Cyclicity of torsion left `D_k(A)`-modules. With `k` and `A` as above, let `M` be a finitely
generated left `D_k(A)`-module in which every element is killed by a nonzero operator. For every
`x ∈ M` and every nonzero `t ∈ D_k(A)` there is `h ∈ M` with `M = D_k(A) (x + t h)`; in
particular `M` is cyclic. -/
def DiffOpCyclicLeftStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
    (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.Smooth k A]
    (M : Type v) [AddCommGroup M] [Module (diffOps k A) M]
    [Module.Finite (diffOps k A) M],
    (∀ m : M, ∃ s : diffOps k A, s ≠ 0 ∧ s • m = 0) →
    ∀ (x : M) (t : diffOps k A), t ≠ 0 →
      ∃ h : M, Submodule.span (diffOps k A) {x + t • h} = ⊤

/-- Two generators for right ideals of `D_k(A)`. -/
theorem diffOpTwoGeneratedRight : DiffOpTwoGeneratedRightStatement.{u} := by
  sorry

/-- Two generators for left ideals of `D_k(A)`. -/
theorem diffOpTwoGeneratedLeft : DiffOpTwoGeneratedLeftStatement.{u} := by
  sorry

/-- Theorem A for `D_k(A)`, right and left forms. -/
theorem diffOpFixedAnchor : DiffOpFixedAnchorStatement.{u} := by
  sorry

/-- The Global Stafford identity for `D_k(A)`. -/
theorem diffOpGlobalStafford : DiffOpGlobalStaffordStatement.{u} := by
  sorry

/-- Finitely generated torsion right `D_k(A)`-modules are cyclic. -/
theorem diffOpCyclicRight : DiffOpCyclicRightStatement.{u, v} := by
  sorry

/-- Finitely generated torsion left `D_k(A)`-modules are cyclic. -/
theorem diffOpCyclicLeft : DiffOpCyclicLeftStatement.{u, v} := by
  sorry

end GeneralizedStaffordChallenge
