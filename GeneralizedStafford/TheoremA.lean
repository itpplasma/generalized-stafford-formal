module

public import GeneralizedStafford.Descent

@[expose] public section

/-!
# Theorem A' (fixed ideal) and Theorem A (fixed anchor)

Paper: `docs/core-theorem.md`, Section 1 (statements) and Section 4;
manuscript `docs/manuscript/main.tex`, Theorems A' and A (introduction) and
Section 4 (`sec:descent`, proofs of Theorem A' and Theorem A).

Assume (S) `R` simple, (N) right Noetherian, and (Z) `k` an infinite central
field. Zero divisors are allowed: the anchor `d` and the element witnessing
(Reg_I) are regular, while the tails `t` and `a` need only be nonzero.

* **Theorem A'** (`fixed_ideal`) is `P(N+1)` of the two-call descent with the
  empty family of tests: `Kdim R/(I + fR) < 0`, i.e. `I + fR = R`.
* **Theorem A** (`fixed_anchor`) is Theorem A' for `I = dR`, `x = B d` and
  `t = a d` (nonzero because `d` is regular): `dR + (B d + H a d)R = R` reads
  `1 = d U + (B + H a) d V`.
-/

namespace GeneralizedStafford

open MulOpposite nonZeroDivisors AlgebraicAnalysis.DenominatorTorsion

universe u

variable {R : Type u} [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
variable {k : Type*} [Field k] [Infinite k] [Algebra k R]

include k in
/-- **Theorem A' (fixed ideal).** Let `I` be a right ideal containing a
regular element (Reg_I) with `Kdim(R/I) ≤ N` finite (Fin_I). For every `x ∈ R`
and every `t ≠ 0` there is `H ∈ R` with `I + (x + H t)R = R`. -/
theorem fixed_ideal {I : Submodule Rᵐᵒᵖ R} (hreg : ∃ s ∈ I, s ∈ R⁰)
    {N : ℕ} (hfin : Module.DevLE Rᵐᵒᵖ N (R ⧸ I)) (x : R) {t : R} (ht : t ≠ 0) :
    ∃ H : R, I ⊔ principalRightIdeal (x + H * t) = ⊤ := by
  obtain ⟨H, hsmall, -⟩ := idealBound_zero (k := k) hreg hfin x t ht
    (fun i : PEmpty.{u + 1} => nomatch i)
  exact ⟨H, eq_top_of_small_zero hsmall⟩

include k in
/-- **Theorem A (fixed anchor).** Let `d` be regular with
`δ(d) = Kdim(R/dR) ≤ N` finite. For every `a ≠ 0` (possibly a zero-divisor)
and every `B` there are `H, U, V` with `1 = d U + (B + H a) d V`. -/
theorem fixed_anchor {d : R} (hd : d ∈ R⁰) {N : ℕ}
    (hfin : Module.DevLE Rᵐᵒᵖ N (R ⧸ principalRightIdeal d)) {a : R} (ha : a ≠ 0) (B : R) :
    ∃ H U V : R, 1 = d * U + (B + H * a) * d * V := by
  obtain ⟨H, hH⟩ := fixed_ideal (k := k) (I := principalRightIdeal d)
    ⟨d, ⟨1, mul_one d⟩, hd⟩ hfin (B * d) (t := a * d) (fun h0 => ha (hd.2 a h0))
  have h1 : (1 : R) ∈ principalRightIdeal d ⊔ principalRightIdeal (B * d + H * (a * d)) := by
    rw [hH]; exact Submodule.mem_top
  obtain ⟨y, ⟨U, rfl⟩, z, ⟨V, rfl⟩, he⟩ := Submodule.mem_sup.mp h1
  refine ⟨H, U, V, ?_⟩
  rw [← he]
  change d * U + (B * d + H * (a * d)) * V = d * U + (B + H * a) * d * V
  simp only [add_mul, mul_assoc]

end GeneralizedStafford
