module

public import GeneralizedStafford.TheoremA

@[expose] public section

/-!
# Corollary B: rings of deviation at most `ω`

**Statement.** If `R` is right Noetherian with `Kdim R ≤ ω`, then
`δ(d) = Kdim(R/dR)` is finite for every regular `d`, and `Kdim(R/I)` is finite
for every right ideal `I` containing a regular element; hence Theorems A and
A' hold for all such `d` and `I` under (S), (N), (Z).

**Proof idea.** Left multiplication by a regular `d` is an injective
endomorphism of `R_R` with image `dR`. In the descending chain
`R ⊇ dR ⊇ d²R ⊇ ⋯` every factor is isomorphic to `R/dR`, so by the definition
of `Kdim R ≤ ω` the factor `R/dR` has finite deviation
(`Module.DevLEOmega.quotient_range_of_injective`). A right ideal containing a
regular `s` contains `sR`, so `R/I` is a quotient of `R/sR`.
-/

namespace GeneralizedStafford

open MulOpposite nonZeroDivisors AlgebraicAnalysis AlgebraicAnalysis.DenominatorTorsion

universe u

variable {R : Type u} [Ring R]

/-- **Principal quotients.** If `Kdim R ≤ ω`, then `R/dR` has
finite deviation for every regular `d`. -/
theorem principal_quotient_finite_of_omega (homega : Module.DevLEOmega Rᵐᵒᵖ R)
    {d : R} (hd : d ∈ R⁰) : ∃ N, Module.DevLE Rᵐᵒᵖ N (R ⧸ principalRightIdeal d) :=
  homega.quotient_range_of_injective (leftMulLinear d) fun x y hxy => by
    have h : d * (x - y) = 0 := by
      rw [mul_sub]
      exact sub_eq_zero.mpr hxy
    exact sub_eq_zero.mp (hd.1 _ h)

/-- **Hypothesis (H_all).** If `Kdim R ≤ ω`, then (H_all) holds. -/
theorem principalQuotientsFinite_of_devLE_omega (homega : Module.DevLEOmega Rᵐᵒᵖ R) :
    PrincipalQuotientsFinite R :=
  fun _ hd => principal_quotient_finite_of_omega homega hd

/-- **Right ideals.** If `Kdim R ≤ ω`, then `R/I` has finite deviation for
every right ideal `I` containing a regular element. -/
theorem quotient_finite_of_omega (homega : Module.DevLEOmega Rᵐᵒᵖ R)
    {I : Submodule Rᵐᵒᵖ R} (hreg : ∃ s ∈ I, s ∈ R⁰) :
    ∃ N, Module.DevLE Rᵐᵒᵖ N (R ⧸ I) := by
  obtain ⟨s, hsI, hs⟩ := hreg
  obtain ⟨N, hN⟩ := principal_quotient_finite_of_omega homega hs
  exact ⟨N, devLE_quotient_of_le hN (principalRightIdeal_le hsI)⟩

variable [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
variable {k : Type*} [Field k] [Infinite k] [Algebra k R]

include k in
/-- **Corollary B for Theorem A'.** If `Kdim R ≤ ω` and `I` contains a regular
element, then for every `x` and `t ≠ 0` there is `H` with
`I + (x + H t)R = R`. -/
theorem fixed_ideal_of_devLE_omega (homega : Module.DevLEOmega Rᵐᵒᵖ R)
    {I : Submodule Rᵐᵒᵖ R} (hreg : ∃ s ∈ I, s ∈ R⁰) (x : R) {t : R} (ht : t ≠ 0) :
    ∃ H : R, I ⊔ principalRightIdeal (x + H * t) = ⊤ := by
  obtain ⟨N, hfin⟩ := quotient_finite_of_omega homega hreg
  exact fixed_ideal (k := k) hreg hfin x ht

include k in
/-- **Corollary B for Theorem A.** If `Kdim R ≤ ω`, then for every regular `d`,
every `a ≠ 0` and every `B` there are `H, U, V` with `1 = d U + (B + H a) d V`. -/
theorem fixed_anchor_of_devLE_omega (homega : Module.DevLEOmega Rᵐᵒᵖ R)
    {d : R} (hd : d ∈ R⁰) {a : R} (ha : a ≠ 0) (B : R) :
    ∃ H U V : R, 1 = d * U + (B + H * a) * d * V := by
  obtain ⟨N, hfin⟩ := principal_quotient_finite_of_omega homega hd
  exact fixed_anchor (k := k) hd hfin ha B

end GeneralizedStafford
