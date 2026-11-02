import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Order.SupIndep
import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.FreeAlgebra
import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# Affine generation over simple Noetherian rings with infinite centre

This file states Theorem A', Theorem A and Corollaries B and C (C.1, C.2 and
C.3), and the two-generation statements for the Weyl algebra (last section).
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

Left-ideal statements are stated only for the Weyl algebra (last section): there
the left case is the right case transported by the transposition anti-automorphism.
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

/-- The Goldie-torsion part `t(M)` of `M`: the right submodule spanned by the
elements `m` with `m s = 0` for some regular `s`. Under (S) and (N) these
elements already form a submodule (Goldie's theorem); the span is used so
that no closure proof enters the statement. -/
def goldieTorsionPart : Submodule Rᵐᵒᵖ M :=
  Submodule.span Rᵐᵒᵖ {m : M | ∃ s : R, IsRegularElement s ∧ op s • m = 0}

/-- `UDimGE R M n`: the uniform (Goldie) dimension of `M` is at least `n`, that
is, `M` contains `n` nonzero right submodules whose sum is direct. -/
def UDimGE (n : ℕ) : Prop :=
  ∃ N : Fin n → Submodule Rᵐᵒᵖ M, iSupIndep N ∧ ∀ i, N i ≠ ⊥

/-- `UDimLE R M n`: the uniform (Goldie) dimension of `M` is at most `n`, that
is, `M` contains no direct sum of `n + 1` nonzero right submodules. -/
def UDimLE (n : ℕ) : Prop :=
  ¬ UDimGE R M (n + 1)

/-- `SpanRankLE R M m`: the right module `M` is generated by at most `m`
elements, i.e. `μ_R(M) ≤ m`. -/
def SpanRankLE (m : ℕ) : Prop :=
  ∃ s : Finset M, s.card ≤ m ∧ Submodule.span Rᵐᵒᵖ (s : Set M) = ⊤

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

/-- **Corollary B, dimension part.** Let `R` be right Noetherian
with `Kdim R ≤ ω` (H_omega). Then `δ(d) = Kdim(R/dR)` is a finite integer for
every regular `d` (so (H_all) holds), and `Kdim(R/I)` is a finite integer for
every right ideal `I` containing a regular element. The ordinal refinement
`δ(d) < Kdim R` is deliberately not stated. -/
def CorollaryBDimensionStatement : Prop :=
  ∀ (R : Type u) [Ring R] [IsNoetherian Rᵐᵒᵖ R], HOmega R →
    HAll R ∧ ∀ I : Submodule Rᵐᵒᵖ R, (∃ s ∈ I, IsRegularElement s) →
      HasFiniteDevDim R (R ⧸ I)

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

/-- Corollary B, dimension part. -/
theorem corollaryB_dimension : CorollaryBDimensionStatement.{u} := by
  sorry

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

/-- Existence of `a ∈ I` with `aQ = IQ` (first step of Corollary C.2). -/
theorem corollaryC2_fullRank : CorollaryC2FullRankStatement.{u} := by
  sorry

/-- Corollary C.2, prescribed form. -/
theorem corollaryC2_prescribed : CorollaryC2PrescribedStatement.{u} := by
  sorry

/-- Corollary C.2, every right ideal is two-generated. -/
theorem corollaryC2 : CorollaryC2Statement.{u} := by
  sorry

/-! ## Corollary C.3

The classical right quotient ring is `Q = M_s(D)`, and the normalized Goldie rank is
`ρ(M) = length_Q(M ⊗_R Q) / s` for finitely generated `M`. Under (S) and (N)
(Goldie's theorem) the two numbers are uniform dimensions:

* `s = udim(R_R)`, since `R_R` is essential in `Q_R` and `Q_Q` is a direct
  sum of `s` simple right ideals;
* `length_Q(M ⊗_R Q) = udim(M / t(M))`, where `t(M)` is the Goldie-torsion
  part: `M ⊗_R Q ≅ (M/t(M)) ⊗_R Q` by flatness of `Q`, the torsion-free module
  `N = M/t(M)` is an essential `R`-submodule of `N ⊗_R Q`, and for a
  `Q`-module the uniform dimension over `R` equals the `Q`-length.

Hence `ρ(M) = udim(M/t(M)) / udim(R_R)`. Writing `ℓ = udim(M/t(M))` and
`s = udim(R_R)`, the two bounds are stated without division or rounding:

* `⌈ρ(M)⌉ ≤ μ(M)` iff `ℓ ≤ μ(M) s`: if `M` is generated by `m` elements,
  `udim(M/t(M)) ≥ ℓ` and `udim(R_R) ≤ s`, then `ℓ ≤ m s`;
* `μ(M) ≤ ⌊ρ(M)⌋ + 1` iff `M` is generated by `q` elements for every `q` with
  `ℓ < q s` (the least such `q` is `⌊ℓ/s⌋ + 1`): if `udim(M/t(M)) ≤ ℓ`,
  `udim(R_R) ≥ s` and `ℓ < q s`, then `M` is generated by `q` elements. -/

/-- **Corollary C.3, lower bound** `⌈ρ(M)⌉ ≤ μ(M)`. Let `R` satisfy (S) and (N)
and let `M` be a finitely generated right module. If `M` is generated by `m`
elements, `M/t(M)` contains a direct sum of `ℓ` nonzero submodules and `R_R`
contains no direct sum of `s + 1` nonzero right ideals, then `ℓ ≤ m s`.
This is equivalent to `⌈ρ(M)⌉ ≤ μ(M)` given the classical identities
`s = udim R_R` and `length_Q(M ⊗ Q) = udim(M/t(M))` (Goldie; McConnell--Robson, 2.2--2.3); it
is not a literal formalization of `ρ`. -/
def CorollaryC3LowerStatement : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M]
    (m ℓ s : ℕ),
    SpanRankLE R M m → UDimGE R (M ⧸ goldieTorsionPart R M) ℓ → UDimLE R R s →
      ℓ ≤ m * s

/-- **Corollary C.3, upper bound** `μ(M) ≤ ⌊ρ(M)⌋ + 1`. Let `R` satisfy (S), (N),
(Z) and (H_all) and let `M` be a finitely generated right module. If `M/t(M)`
contains no direct sum of `ℓ + 1` nonzero submodules, `R_R` contains a direct
sum of `s` nonzero right ideals, and `ℓ < q s`, then `M` is generated by `q`
elements. This is equivalent to `μ(M) ≤ ⌊ρ(M)⌋ + 1` given the classical
identities `s = udim R_R` and `length_Q(M ⊗ Q) = udim(M/t(M))` (Goldie; McConnell--Robson, 2.2--2.3); it is not a literal
formalization of `ρ`. -/
def CorollaryC3UpperStatement : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    [Infinite (Subring.center R)], HAll R →
    ∀ (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M]
      (q ℓ s : ℕ),
      UDimLE R (M ⧸ goldieTorsionPart R M) ℓ → UDimGE R R s → ℓ < q * s →
        SpanRankLE R M q

/-- Corollary C.3, lower bound. -/
theorem corollaryC3_lower : CorollaryC3LowerStatement.{u, v} := by
  sorry

/-- Corollary C.3, upper bound. -/
theorem corollaryC3_upper : CorollaryC3UpperStatement.{u, v} := by
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
