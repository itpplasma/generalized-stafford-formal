module

public import AlgebraicAnalysis.Module.DeviationOmega
public import AlgebraicAnalysis.RingTheory.Goldie.Torsion

@[expose] public section

/-!
# Conventions and the deviation facts used throughout

* Modules are **right** modules: a right `R`-module `M` is `[Module Rᵐᵒᵖ M]`,
  and `m r` is written `op r • m`. A right ideal is a `Submodule Rᵐᵒᵖ R`;
  `principalRightIdeal x` is `xR` and `I ⊔ J` is `I + J`.
* (S) is `[IsSimpleRing R]`, (N) is `[IsNoetherian Rᵐᵒᵖ R]`, and (Z) is
  supplied as an infinite field `k` with `[Algebra k R]`, i.e. `k` is central.
* A regular element is a two-sided non-zero-divisor, `d ∈ R⁰`.
* `Kdim M ≤ n` is the deviation bound `Module.DevLE Rᵐᵒᵖ n M`, and the
  strict stratum `Kdim M < e` is `Module.Small Rᵐᵒᵖ e M`; so `Small (n + 1)` is
  `DevLE n` and `Small 0` means `M = 0`.
* Goldie torsion is `AlgebraicAnalysis.Goldie.IsGoldieTorsion`; Goldie's
  theorem is proved in `AlgebraicAnalysis.RingTheory.Goldie`.

This file states the hypothesis (H_all) and collects the elementary deviation
facts used by several sections: quotients of `R/dR` inherit its bound, a cyclic
module `uR` is `R/ann(u)`, and `R/J` of deviation `< 0` means `J = R`.
-/

namespace GeneralizedStafford

open MulOpposite AlgebraicAnalysis AlgebraicAnalysis.DenominatorTorsion

universe u v

variable {R : Type u} [Ring R]

/-- Hypothesis (H_all): `δ(d) = Kdim(R/dR)` is finite for every regular `d`.

The name `HAll` is taken by the challenge's own copy of this hypothesis,
`GeneralizedStaffordChallenge.HAll`, which the transport file restates while
opening this namespace; the library predicate keeps a descriptive name to
avoid that clash, and `GeneralizedStaffordChallenge.hAll_iff` identifies the
two. -/
def PrincipalQuotientsFinite (R : Type u) [Ring R] : Prop :=
  ∀ d : R, d ∈ nonZeroDivisors R → ∃ N, Module.DevLE Rᵐᵒᵖ N (R ⧸ principalRightIdeal d)

/-- A right ideal `X ⊇ dR` inherits the deviation bound of `R/dR`: `R/X` is a
quotient of `R/dR`. -/
theorem devLE_quotient_of_le {n : ℕ} {d : R}
    (hd : Module.DevLE Rᵐᵒᵖ n (R ⧸ principalRightIdeal d))
    {X : Submodule Rᵐᵒᵖ R} (hX : principalRightIdeal d ≤ X) :
    Module.DevLE Rᵐᵒᵖ n (R ⧸ X) :=
  hd.of_surjective (Submodule.factor hX) (Submodule.factor_surjective hX)

/-- A right ideal containing `s` contains `sR`. -/
theorem principalRightIdeal_le {X : Submodule Rᵐᵒᵖ R} {s : R} (hs : s ∈ X) :
    principalRightIdeal s ≤ X := by
  rintro y ⟨r, rfl⟩
  exact X.smul_mem (op r) hs

/-- If `R/J` has deviation `< 0`, that is `R/J = 0`, then `J = R`. -/
theorem eq_top_of_small_zero {J : Submodule Rᵐᵒᵖ R}
    (h : Module.Small Rᵐᵒᵖ 0 (R ⧸ J)) : J = ⊤ := by
  have h1 : (1 : R) ∈ J := (Submodule.Quotient.mk_eq_zero J).mp (h.elim _ _)
  refine eq_top_iff.mpr fun y _ => ?_
  simpa using J.smul_mem (op y) h1

section Cyclic

variable {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- The cyclic map `r ↦ u r` of a right module; its range is `uR` and its
kernel is the right annihilator `ann(u)`, so `uR ≅ R/ann(u)`. -/
def cyclicMap (u : M) : R →ₗ[Rᵐᵒᵖ] M where
  toFun r := op r • u
  map_add' r s := by rw [op_add, add_smul]
  map_smul' a r := by
    change op (r * unop a) • u = a • (op r • u)
    rw [op_mul, op_unop, mul_smul]

/-- The range of `r ↦ u r` is the cyclic submodule `uR`. -/
theorem range_cyclicMap (u : M) :
    LinearMap.range (cyclicMap (R := R) u) = Submodule.span Rᵐᵒᵖ {u} := by
  ext m
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩; exact ⟨op r, rfl⟩
  · rintro ⟨a, rfl⟩; exact ⟨unop a, by change op (unop a) • u = a • u; rw [op_unop]⟩

/-- `Kdim(R/ann(u)) = Kdim(uR)`: the two modules are isomorphic. -/
theorem devLE_quotient_ker_cyclicMap_iff (n : ℕ) (u : M) :
    Module.DevLE Rᵐᵒᵖ n (R ⧸ LinearMap.ker (cyclicMap (R := R) u)) ↔
      Module.DevLE Rᵐᵒᵖ n (Submodule.span Rᵐᵒᵖ {u}) :=
  (Module.devLE_linearEquiv_iff n (cyclicMap (R := R) u).quotKerEquivRange).trans
    (Module.devLE_linearEquiv_iff n (LinearEquiv.ofEq _ _ (range_cyclicMap (R := R) u)))

end Cyclic

end GeneralizedStafford
