import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Order.SupIndep

/-!
# Affine generation over simple Noetherian rings with infinite centre

This file states Theorem A', Theorem A and Corollaries B and C of the research
note `docs/core-theorem.md` (Sections 0, 1 and 6) and of the manuscript
`docs/manuscript/main.tex` (introduction and Section 6, "Module
consequences"). It imports only Mathlib and defines everything else inline.

## Conventions (core-theorem.md, C1--C5)

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
* `IsRegularElement d` is two-sided regularity (C2): `d x = 0 → x = 0` and
  `x d = 0 → x = 0`. It is literally Mathlib's membership `d ∈ R⁰`
  (`mem_nonZeroDivisors_iff` holds by `Iff.rfl`); it is spelled out here so
  that a reader need not look up the sidedness of `nonZeroDivisors`.
* `KrullDimLE R M n` is the right **Gabriel--Rentschler (deviation)
  dimension** bound `Kdim M ≤ n` of C3, defined on the lattice of right
  submodules: `Kdim ≤ 0` means that every descending chain stabilizes, and
  `Kdim ≤ n + 1` means that for every descending chain
  `M₀ ≥ M₁ ≥ ⋯` all but finitely many factors `Mᵢ/Mᵢ₊₁` have `Kdim ≤ n`.
  The factor `Mᵢ/Mᵢ₊₁` is represented by the interval `[Mᵢ₊₁, Mᵢ]` of the
  submodule lattice, which is order isomorphic to its submodule lattice.
  The zero module satisfies every bound, so "`Kdim M` is a finite integer
  `≥ -1`" is `∃ n : ℕ, KrullDimLE R M n` (`HasFiniteKrullDim`).
  This is **not** the classical (Krull) dimension of chains of prime ideals
  and not Mathlib's `ringKrullDim`/`Module.length`; it is the deviation of
  the submodule poset. `KrullDimLEOmega R M` is `Kdim M ≤ ω`: for every
  descending chain all but finitely many factors have finite dimension.
* `IsGoldieTorsion R M` (C4): every `m` has `m s = 0` for some regular `s`.
* (S) is Mathlib's `IsSimpleRing R` (nonzero, only the trivial two-sided
  ideals). (N) is `IsNoetherian Rᵐᵒᵖ R`: right ideals satisfy the ascending
  chain condition. (Z) is `Infinite (Subring.center R)`: the centre is
  infinite. Under (S) the centre is a field (Mathlib's
  `IsSimpleRing.isField_center`), so (Z) is the same as "`R` is an algebra
  over an infinite central field", as remarked after C5.
* Finitely generated right modules are `[Module.Finite Rᵐᵒᵖ M]`.

Rings live in universe `u` and modules in universe `v`; the theorems are
stated for all universes. The compared theorems are the `theorem`s below;
each `sorry` is a deliberate hole filled by `Solution.lean`.

Opposite-side statements (left ideals, left modules) are not stated: they
require the hypotheses for `Rᵐᵒᵖ` and are remarks, not corollaries
(core-theorem.md Remark 6.5).
-/

universe u v

namespace GeneralizedStaffordChallenge

open MulOpposite

/-! ## Regular elements, deviation and Goldie torsion -/

section Definitions

variable (R : Type u) [Ring R]

/-- An element `d` of `R` is **regular** if it is a two-sided non-zero-divisor:
`d x = 0` implies `x = 0`, and `x d = 0` implies `x = 0` (convention C2).
This is definitionally Mathlib's `d ∈ R⁰`. -/
def IsRegularElement {R : Type u} [Ring R] (d : R) : Prop :=
  (∀ x : R, d * x = 0 → x = 0) ∧ (∀ x : R, x * d = 0 → x = 0)

/-- Finite Gabriel--Rentschler deviation of a partial order. `PosetDevLE 0 α`
says that every descending chain in `α` stabilizes; `PosetDevLE (n + 1) α`
says that for every descending chain `c₀ ≥ c₁ ≥ ⋯` all but finitely many
closed intervals `[cᵢ₊₁, cᵢ]` satisfy `PosetDevLE n`. -/
def PosetDevLE : (n : ℕ) → (α : Type v) → [PartialOrder α] → Prop
  | 0, α, _ => ∀ c : ℕ → α, Antitone c → ∃ N, ∀ i, N ≤ i → c i = c N
  | n + 1, α, _ => ∀ c : ℕ → α, Antitone c →
      ∃ N, ∀ i, N ≤ i → PosetDevLE n (Set.Icc (c (i + 1)) (c i))

variable (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- `KrullDimLE R M n`: the right module `M` has right Gabriel--Rentschler
(deviation) dimension `Kdim M ≤ n` (convention C3), defined on the lattice of
right submodules of `M`. -/
def KrullDimLE (n : ℕ) : Prop :=
  PosetDevLE n (Submodule Rᵐᵒᵖ M)

/-- `Kdim M` is a finite integer (possibly `-1`, which happens exactly when
`M = 0`). -/
def HasFiniteKrullDim : Prop :=
  ∃ n : ℕ, KrullDimLE R M n

/-- `KrullDimLEOmega R M`: `Kdim M ≤ ω`, that is, for every descending chain of
right submodules `M₀ ≥ M₁ ≥ ⋯` all but finitely many factors `Mᵢ/Mᵢ₊₁`
(the intervals `[Mᵢ₊₁, Mᵢ]`) have finite deviation. -/
def KrullDimLEOmega : Prop :=
  ∀ c : ℕ → Submodule Rᵐᵒᵖ M, Antitone c → ∃ N, ∀ i, N ≤ i →
    ∃ n : ℕ, PosetDevLE n (Set.Icc (c (i + 1)) (c i))

/-- `M` is **Goldie-torsion** (convention C4): every `m ∈ M` satisfies
`m s = 0` for some regular `s ∈ R`. -/
def IsGoldieTorsion : Prop :=
  ∀ m : M, ∃ s : R, IsRegularElement s ∧ op s • m = 0

/-- The Goldie-torsion part `t(M)` of `M`: the right submodule spanned by the
elements `m` with `m s = 0` for some regular `s`. Under (S) and (N) these
elements already form a submodule (Goldie's theorem, I1); the span is used so
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

/-- `GeneratedBy R M m`: the right module `M` is generated by at most `m`
elements, i.e. `μ_R(M) ≤ m`. -/
def GeneratedBy (m : ℕ) : Prop :=
  ∃ s : Finset M, s.card ≤ m ∧ Submodule.span Rᵐᵒᵖ (s : Set M) = ⊤

/-- Hypothesis (H_all): `δ(d) = Kdim(R/dR)` is a finite integer for every
regular `d`. -/
def HAll : Prop :=
  ∀ d : R, IsRegularElement d → HasFiniteKrullDim R (R ⧸ Submodule.span Rᵐᵒᵖ {d})

/-- Hypothesis (H_omega): `Kdim R ≤ ω` for the right regular module `R_R`. -/
def HOmega : Prop :=
  KrullDimLEOmega R R

end Definitions

/-! ## Theorem A' and Theorem A -/

/-- **Theorem A' (fixed ideal).** Let `R` be a simple (S), right Noetherian (N)
ring with infinite centre (Z). Let `I` be a right ideal containing a regular
element (Reg_I) such that `Kdim(R/I)` is a finite integer (Fin_I). Then for
every `x ∈ R` and every nonzero `t ∈ R` there is `H ∈ R` with
`I + (x + H t)R = R`. -/
def FixedIdealStatement : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    [Infinite (Subring.center R)] (I : Submodule Rᵐᵒᵖ R),
    (∃ s ∈ I, IsRegularElement s) → HasFiniteKrullDim R (R ⧸ I) →
    ∀ x t : R, t ≠ 0 →
      ∃ H : R, I ⊔ Submodule.span Rᵐᵒᵖ {x + H * t} = ⊤

/-- **Theorem A (fixed anchor).** Let `R` satisfy (S), (N), (Z) and let `d` be a
regular element with `δ(d) = Kdim(R/dR)` a finite integer. For every nonzero
`a ∈ R` (possibly a zero-divisor) and every `B ∈ R` there are `H, U, V ∈ R`
with `1 = d U + (B + H a) d V`. -/
def FixedAnchorStatement : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    [Infinite (Subring.center R)] (d : R),
    IsRegularElement d → HasFiniteKrullDim R (R ⧸ Submodule.span Rᵐᵒᵖ {d}) →
    ∀ a B : R, a ≠ 0 →
      ∃ H U V : R, 1 = d * U + (B + H * a) * d * V

/-- Theorem A' (fixed ideal), core-theorem.md Section 1. -/
theorem fixedIdeal : FixedIdealStatement.{u} := by
  sorry

/-- Theorem A (fixed anchor), core-theorem.md Section 1. -/
theorem fixedAnchor : FixedAnchorStatement.{u} := by
  sorry

/-! ## Corollary B (Lemma 6.1) -/

/-- **Corollary B, dimension part (Lemma 6.1).** Let `R` be right Noetherian
with `Kdim R ≤ ω` (H_omega). Then `δ(d) = Kdim(R/dR)` is a finite integer for
every regular `d` (so (H_all) holds), and `Kdim(R/I)` is a finite integer for
every right ideal `I` containing a regular element. -/
def CorollaryBDimensionStatement : Prop :=
  ∀ (R : Type u) [Ring R] [IsNoetherian Rᵐᵒᵖ R], HOmega R →
    HAll R ∧ ∀ I : Submodule Rᵐᵒᵖ R, (∃ s ∈ I, IsRegularElement s) →
      HasFiniteKrullDim R (R ⧸ I)

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

/-- Corollary B, dimension part (Lemma 6.1). -/
theorem corollaryB_dimension : CorollaryBDimensionStatement.{u} := by
  sorry

/-- Corollary B for Theorem A. -/
theorem corollaryB_fixedAnchor : CorollaryBFixedAnchorStatement.{u} := by
  sorry

/-- Corollary B for Theorem A'. -/
theorem corollaryB_fixedIdeal : CorollaryBFixedIdealStatement.{u} := by
  sorry

/-! ## Corollary C.1 (core Lemma 6.2; manuscript Proposition 6.2, `prop:C1`) -/

/-- **Corollary C.1 (prescribed cyclic generator).** Let `R` satisfy (S), (N),
(Z) and let `M` be a finitely generated Goldie-torsion right module with
`Kdim M` a finite integer. For every `x ∈ M` and every nonzero `t ∈ R` there
is `h ∈ M` with `M = (x + h t)R`. -/
def CorollaryC1Statement : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    [Infinite (Subring.center R)]
    (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M],
    IsGoldieTorsion R M → HasFiniteKrullDim R M →
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

/-- **Corollary C.1, stable cyclicity** (manuscript Proposition 6.2(a),
`prop:C1`). Let `R` satisfy (S), (N), (Z), let `c, u` be Goldie-torsion elements of a right module
`M` (each is killed by a regular element) with `Kdim(uR)` a finite integer.
For every nonzero `t ∈ R` there is `H ∈ R` with `cR + uR = (c + u H t)R`. -/
def CorollaryC1StableStatement : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    [Infinite (Subring.center R)]
    (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] (c u : M),
    (∃ s : R, IsRegularElement s ∧ op s • c = 0) →
    (∃ s : R, IsRegularElement s ∧ op s • u = 0) →
    HasFiniteKrullDim R (Submodule.span Rᵐᵒᵖ {u}) →
    ∀ t : R, t ≠ 0 →
      ∃ H : R, Submodule.span Rᵐᵒᵖ {c, u} = Submodule.span Rᵐᵒᵖ {c + op (H * t) • u}

/-- Corollary C.1 (finite dimension hypothesis), core-theorem.md Lemma 6.2. -/
theorem corollaryC1 : CorollaryC1Statement.{u, v} := by
  sorry

/-- Corollary C.1 under (H_all). -/
theorem corollaryC1_hAll : CorollaryC1HAllStatement.{u, v} := by
  sorry

/-- Corollary C.1 under (H_omega). -/
theorem corollaryC1_omega : CorollaryC1OmegaStatement.{u, v} := by
  sorry

/-- Corollary C.1, stable cyclicity (manuscript Proposition 6.2(a), `prop:C1`). -/
theorem corollaryC1_stable : CorollaryC1StableStatement.{u, v} := by
  sorry

/-! ## Corollary C.2 (core Lemma 6.3; manuscript Proposition 6.3, `prop:C2`)

The paper's condition `aQ = IQ` (with `Q` the classical right quotient ring)
is stated elementwise: `a ∈ I` and every `y ∈ I` has a regular `s` with
`y s ∈ aR`. Under (S), (N) these are equivalent: `aQ ⊆ IQ` because `a ∈ I`,
and `y ∈ aQ` iff `y = a r s⁻¹` iff `y s = a r` for some `r` and regular `s`. -/

/-- **Existence of a full-rank element** (first step of Lemma 6.3). Let `R`
satisfy (S) and (N). Every right ideal `I` contains an `a` with `aQ = IQ`, that
is, every `y ∈ I` has a regular `s` with `y s ∈ aR`. -/
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

/-- Existence of `a ∈ I` with `aQ = IQ` (Lemma 6.3, first step). -/
theorem corollaryC2_fullRank : CorollaryC2FullRankStatement.{u} := by
  sorry

/-- Corollary C.2, prescribed form (Lemma 6.3). -/
theorem corollaryC2_prescribed : CorollaryC2PrescribedStatement.{u} := by
  sorry

/-- Corollary C.2, every right ideal is two-generated. -/
theorem corollaryC2 : CorollaryC2Statement.{u} := by
  sorry

/-! ## Corollary C.3 (core Lemma 6.4; manuscript Proposition 6.4, `prop:C3`)

The paper writes the classical right quotient ring as `Q = M_s(D)` and sets
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
contains no direct sum of `s + 1` nonzero right ideals, then `ℓ ≤ m s`. -/
def CorollaryC3LowerStatement : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M]
    (m ℓ s : ℕ),
    GeneratedBy R M m → UDimGE R (M ⧸ goldieTorsionPart R M) ℓ → UDimLE R R s →
      ℓ ≤ m * s

/-- **Corollary C.3, upper bound** `μ(M) ≤ ⌊ρ(M)⌋ + 1`. Let `R` satisfy (S), (N),
(Z) and (H_all) and let `M` be a finitely generated right module. If `M/t(M)`
contains no direct sum of `ℓ + 1` nonzero submodules, `R_R` contains a direct
sum of `s` nonzero right ideals, and `ℓ < q s`, then `M` is generated by `q`
elements. -/
def CorollaryC3UpperStatement : Prop :=
  ∀ (R : Type u) [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    [Infinite (Subring.center R)], HAll R →
    ∀ (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M]
      (q ℓ s : ℕ),
      UDimLE R (M ⧸ goldieTorsionPart R M) ℓ → UDimGE R R s → ℓ < q * s →
        GeneratedBy R M q

/-- Corollary C.3, lower bound (Lemma 6.4). -/
theorem corollaryC3_lower : CorollaryC3LowerStatement.{u, v} := by
  sorry

/-- Corollary C.3, upper bound (Lemma 6.4). -/
theorem corollaryC3_upper : CorollaryC3UpperStatement.{u, v} := by
  sorry

end GeneralizedStaffordChallenge
