import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Ring.Subring.Basic

import GeneralizedStafford.Modules

/-!
# Challenge transport: the challenge definitions and their proofs

The definitions and statement definitions of `GeneralizedStaffordChallenge.lean`
(identical copy `Challenge.lean`) are restated verbatim below, in the same
namespace and under the same names, so that the solution never imports the
challenge. The compared `theorem`s of the challenge are not restated: each
challenge theorem `<name>` is proved here as `<name>_proof`, and
`GeneralizedStaffordSolution.lean` restates it under its challenge name.

The bridge lemmas translate the challenge conventions into those of the
library: `Submodule.span Rᵐᵒᵖ {d}` is `principalRightIdeal d`
(`span_singleton_eq`), `IsRegularElement d` is `d ∈ R⁰` (`isRegular_iff`), the
deviation bounds are AlgebraicAnalysis' `Module.DevLE` and `Module.DevLEOmega`
(`devDimLE_iff`, `hOmega_iff`), (H_all) is `PrincipalQuotientsFinite`
(`hAll_iff`), the infinite centre becomes an infinite central field
(`withCentre`).
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

/-! ## Bridge lemmas: challenge conventions and library conventions -/

open nonZeroDivisors AlgebraicAnalysis AlgebraicAnalysis.DenominatorTorsion
open GeneralizedStafford

/-- The challenge's deviation bound on a poset is AlgebraicAnalysis' `Order.DevLE`. -/
theorem posetDevLE_iff : ∀ (n : ℕ) (α : Type v) [PartialOrder α],
    PosetDevLE n α ↔ Order.DevLE n α
  | 0, α, _ => Iff.rfl
  | n + 1, α, _ => by
    simp only [PosetDevLE, Order.devLE_succ_iff, posetDevLE_iff n]

/-- `DevDimLE R M n` is `Module.DevLE Rᵐᵒᵖ n M`. -/
theorem devDimLE_iff {R : Type u} [Ring R] {M : Type v} [AddCommGroup M]
    [Module Rᵐᵒᵖ M] (n : ℕ) : DevDimLE R M n ↔ Module.DevLE Rᵐᵒᵖ n M :=
  posetDevLE_iff n _

/-- (H_omega) is `Module.DevLEOmega Rᵐᵒᵖ R`. -/
theorem hOmega_iff {R : Type u} [Ring R] : HOmega R ↔ Module.DevLEOmega Rᵐᵒᵖ R := by
  simp only [HOmega, DevDimLEOmega, Module.DevLEOmega, posetDevLE_iff]

/-- `IsRegularElement d` is `d ∈ R⁰`, by definition. -/
theorem isRegular_iff {R : Type u} [Ring R] (d : R) : IsRegularElement d ↔ d ∈ R⁰ :=
  Iff.rfl

/-- The span of `{d}` is the principal right ideal `dR`. -/
theorem span_singleton_eq {R : Type u} [Ring R] (d : R) :
    Submodule.span Rᵐᵒᵖ {d} = principalRightIdeal d := by
  ext y
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨unop a, rfl⟩
  · rintro ⟨r, rfl⟩; exact ⟨op r, rfl⟩

/-- The challenge's Goldie torsion is AlgebraicAnalysis' Goldie torsion. -/
theorem isGoldieTorsion_iff {R : Type u} [Ring R] {M : Type v} [AddCommGroup M]
    [Module Rᵐᵒᵖ M] :
    GeneralizedStaffordChallenge.IsGoldieTorsion R M ↔
      AlgebraicAnalysis.Goldie.IsGoldieTorsion R M := by
  simp only [GeneralizedStaffordChallenge.IsGoldieTorsion,
    AlgebraicAnalysis.Goldie.IsGoldieTorsion, isRegular_iff]

/-- (H_all) of the challenge is the library's `PrincipalQuotientsFinite`. -/
theorem hAll_iff {R : Type u} [Ring R] : HAll R ↔ PrincipalQuotientsFinite R := by
  simp only [HAll, HasFiniteDevDim, devDimLE_iff, isRegular_iff, PrincipalQuotientsFinite]
  refine forall₂_congr fun d _ => ?_
  rw [span_singleton_eq]

/-- The centre of a simple ring is a field, so (Z) provides an infinite
central field `k` with `[Algebra k R]`, as the library assumes. -/
theorem withCentre (R : Type u) [Ring R] [IsSimpleRing R] [Infinite (Subring.center R)]
    (P : Prop)
    (h : ∀ (k : Type u) [Field k] [Infinite k] [Algebra k R], P) : P := by
  let : Field (Subring.center R) := (IsSimpleRing.isField_center R).toField
  let : Algebra (Subring.center R) R :=
    RingHom.toAlgebra' (Subring.center R).subtype fun c x =>
      (Subring.mem_center_iff.mp c.2 x).symm
  exact h (Subring.center R)

/-! ## Proofs of the challenge statements -/

/-- Theorem A' (fixed ideal), from `GeneralizedStafford.fixed_ideal`. -/
theorem fixedIdeal_proof : FixedIdealStatement.{u} := by
  intro R _ _ _ _ I hreg hfin x t ht
  obtain ⟨N, hN⟩ := hfin
  refine withCentre R _ fun k _ _ _ => ?_
  obtain ⟨H, hH⟩ := fixed_ideal (k := k) (I := I) hreg ((devDimLE_iff N).mp hN) x ht
  exact ⟨H, by rw [span_singleton_eq]; exact hH⟩

/-- Theorem A (fixed anchor), from `GeneralizedStafford.fixed_anchor`. -/
theorem fixedAnchor_proof : FixedAnchorStatement.{u} := by
  intro R _ _ _ _ d hd hfin a B ha
  obtain ⟨N, hN⟩ := hfin
  rw [span_singleton_eq] at hN
  refine withCentre R _ fun k _ _ _ => ?_
  exact fixed_anchor (k := k) hd ((devDimLE_iff N).mp hN) ha B

/-- Corollary B for Theorem A, from `GeneralizedStafford.fixed_anchor_of_devLE_omega`. -/
theorem corollaryB_fixedAnchor_proof : CorollaryBFixedAnchorStatement.{u} := by
  intro R _ _ _ _ homega d a B hd ha
  refine withCentre R _ fun k _ _ _ => ?_
  exact fixed_anchor_of_devLE_omega (k := k) (hOmega_iff.mp homega) hd ha B

/-- Corollary B for Theorem A', from `GeneralizedStafford.fixed_ideal_of_devLE_omega`. -/
theorem corollaryB_fixedIdeal_proof : CorollaryBFixedIdealStatement.{u} := by
  intro R _ _ _ _ homega I hreg x t ht
  refine withCentre R _ fun k _ _ _ => ?_
  obtain ⟨H, hH⟩ := fixed_ideal_of_devLE_omega (k := k) (hOmega_iff.mp homega) hreg x ht
  exact ⟨H, by rw [span_singleton_eq]; exact hH⟩

/-- (H_all) from (H_omega), by `GeneralizedStafford.principalQuotientsFinite_of_devLE_omega`
(McConnell--Robson 6.3.9). -/
theorem hAll_of_omega {R : Type u} [Ring R] [IsNoetherian Rᵐᵒᵖ R] (homega : HOmega R) :
    HAll R :=
  hAll_iff.mpr (principalQuotientsFinite_of_devLE_omega (hOmega_iff.mp homega))

/-- Corollary C.1, from `GeneralizedStafford.prescribed_cyclic`. -/
theorem corollaryC1_proof : CorollaryC1Statement.{u, v} := by
  intro R _ _ _ _ M _ _ _ htor hfin x t ht
  obtain ⟨N, hN⟩ := hfin
  refine withCentre R _ fun k _ _ _ => ?_
  exact prescribed_cyclic (k := k) (isGoldieTorsion_iff.mp htor) ((devDimLE_iff N).mp hN) x ht

/-- Corollary C.1 under (H_all), from `GeneralizedStafford.prescribed_cyclic_of_hAll`. -/
theorem corollaryC1_hAll_proof : CorollaryC1HAllStatement.{u, v} := by
  intro R _ _ _ _ hall M _ _ _ htor x t ht
  refine withCentre R _ fun k _ _ _ => ?_
  exact prescribed_cyclic_of_hAll (k := k) (hAll_iff.mp hall)
    (isGoldieTorsion_iff.mp htor) x ht

/-- Corollary C.1 under (H_omega), from
`GeneralizedStafford.prescribed_cyclic_of_devLE_omega`. -/
theorem corollaryC1_omega_proof : CorollaryC1OmegaStatement.{u, v} := by
  intro R _ _ _ _ homega M _ _ _ htor x t ht
  refine withCentre R _ fun k _ _ _ => ?_
  exact prescribed_cyclic_of_devLE_omega (k := k) (hOmega_iff.mp homega)
    (isGoldieTorsion_iff.mp htor) x ht

/-- Corollary C.1, stable cyclicity, from `GeneralizedStafford.span_pair_eq_span_affine`. -/
theorem corollaryC1_stable_proof : CorollaryC1StableStatement.{u, v} := by
  intro R _ _ _ _ M _ _ c u hc hu hfin t ht
  obtain ⟨N, hN⟩ := hfin
  refine withCentre R _ fun k _ _ _ => ?_
  exact span_pair_eq_span_affine (k := k) c u hc hu ⟨N, (devDimLE_iff N).mp hN⟩ ht

/-- Existence of a full-rank element, from Goldie's theorem
`AlgebraicAnalysis.Goldie.exists_mem_forall_exists_mul_mem`. This is a thin
wrapper: the proof is that AlgebraicAnalysis theorem after translating the challenge's spans and regularity. -/
theorem corollaryC2_fullRank_proof : CorollaryC2FullRankStatement.{u} := by
  intro R _ _ _ I
  simp only [span_singleton_eq, isRegular_iff]
  exact AlgebraicAnalysis.Goldie.exists_mem_forall_exists_mul_mem I

/-- Corollary C.2, prescribed form, from `GeneralizedStafford.two_generated_prescribed`. -/
theorem corollaryC2_prescribed_proof : CorollaryC2PrescribedStatement.{u} := by
  intro R _ _ _ _ hall I a haI hIa y hyI t ht
  refine withCentre R _ fun k _ _ _ => ?_
  simp only [span_singleton_eq] at hIa ⊢
  exact two_generated_prescribed (k := k) (hAll_iff.mp hall) haI hIa hyI ht

/-- Corollary C.2, two generators, from `GeneralizedStafford.two_generated`. -/
theorem corollaryC2_proof : CorollaryC2Statement.{u} := by
  intro R _ _ _ _ hall I
  refine withCentre R _ fun k _ _ _ => ?_
  obtain ⟨a, b, hI⟩ := two_generated (k := k) (hAll_iff.mp hall) I
  refine ⟨a, b, ?_⟩
  rw [Submodule.span_insert, span_singleton_eq, span_singleton_eq]
  exact hI

/-- Corollary C.2 under (H_omega), from `corollaryC2_proof` and `hAll_of_omega`. -/
theorem corollaryC2_omega_proof : CorollaryC2OmegaStatement.{u} := by
  intro R _ _ _ _ homega I
  exact corollaryC2_proof R (hAll_of_omega homega) I

end GeneralizedStaffordChallenge
