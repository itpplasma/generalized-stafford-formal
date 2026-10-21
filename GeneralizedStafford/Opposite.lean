module

/-
Adapted from itpplasma/symplectic-stafford-formal, revision
0e55a8059cc923ef39d6ddb66c5b6f6a2682b46b. Modified 21 October 2026:
generalized filtration hypotheses and migrated to GeneralizedStafford.
Original manuscript section references are retained for correspondence.
-/

public import GeneralizedStafford.Induction
public import Mathlib.Algebra.Module.Equiv.Opposite

@[expose] public section

/-!
# Opposite transport (paper §7.7)

The opposite algebra `Uᵐᵒᵖ` with the same filtration satisfies the standing
hypotheses, with associated graded ring `Gᵒᵖ = G` (commutative).  Hence the
affine same-divisor theorem also holds in `Uᵐᵒᵖ`, which reads in `U` as the
left-handed affine identity `1 = R d + S d (B + a H)`, and its
same-divisor specialization `1 = R d + S d F`.
-/

namespace GeneralizedStafford

open MulOpposite

namespace FilteredAlgebraData

variable {k U G : Type*} [Field k] [Ring U] [Algebra k U] [CommRing G] [Algebra k G]
variable {𝒜 : ℕ → Submodule k G} [GradedAlgebra 𝒜]
variable (D : FilteredAlgebraData k U G 𝒜)

/-- The filtration of `Uᵐᵒᵖ`. -/
def opF (n : ℕ) : Submodule k Uᵐᵒᵖ :=
  (D.F n).comap (opLinearEquiv k : U ≃ₗ[k] Uᵐᵒᵖ).symm.toLinearMap

lemma mem_opF {n : ℕ} {x : Uᵐᵒᵖ} : x ∈ D.opF n ↔ unop x ∈ D.F n := Iff.rfl

/-- The unop map on filtration pieces. -/
def opPiece (n : ℕ) : D.opF n →ₗ[k] D.F n :=
  (opLinearEquiv k : U ≃ₗ[k] Uᵐᵒᵖ).symm.toLinearMap.restrict fun _ hx => hx

lemma opPiece_apply {n : ℕ} (x : D.opF n) : (D.opPiece n x : U) = unop (x : Uᵐᵒᵖ) := rfl

lemma gr_opPiece {n : ℕ} (z : D.opF n) :
    ((D.gr n (D.opPiece n z) : 𝒜 n) : G) = D.grAt n (unop (z : Uᵐᵒᵖ)) :=
  (D.grAt_of_mem z.2).symm

/-- **The opposite filtered algebra** (paper §7.7). -/
def op : FilteredAlgebraData k Uᵐᵒᵖ G 𝒜 where
  F := D.opF
  mono := fun _ _ h _ hx => D.mono h hx
  exhaustive := fun u => D.exhaustive (unop u)
  one_mem_zero := D.one_mem_zero
  mul_mem := fun {i j} _ _ hu hv => by
    rw [mem_opF, unop_mul, add_comm]
    exact D.mul_mem hv hu
  gr := fun n => (D.gr n).comp (D.opPiece n)
  gr_surjective := fun n y => by
    obtain ⟨x, hx⟩ := D.gr_surjective n y
    refine ⟨⟨MulOpposite.op (x : U), x.2⟩, ?_⟩
    rw [LinearMap.comp_apply, show D.opPiece n ⟨MulOpposite.op (x : U), x.2⟩ = x from
      Subtype.ext rfl]
    exact hx
  gr_zero_eq_zero_iff := fun x => by
    rw [LinearMap.comp_apply, D.gr_zero_eq_zero_iff]
    constructor
    · intro h
      apply Subtype.ext
      apply MulOpposite.unop_injective
      have := congrArg Subtype.val h
      simpa [opPiece_apply] using this
    · rintro rfl; rw [map_zero]
  gr_succ_eq_zero_iff := fun n x => by
    rw [LinearMap.comp_apply, D.gr_succ_eq_zero_iff]; rfl
  gr_mul := fun {i j} x y => by
    simp only [LinearMap.comp_apply]
    rw [D.gr_opPiece, D.gr_opPiece, D.gr_opPiece]
    change D.grAt (i + j) (unop ((x : Uᵐᵒᵖ) * y)) = _
    have hx : unop (x : Uᵐᵒᵖ) ∈ D.F i := x.2
    have hy : unop (y : Uᵐᵒᵖ) ∈ D.F j := y.2
    rw [unop_mul, D.grAt_mul' (add_comm j i) hy hx, mul_comm]

variable [IsDomain G] [IsNoetherianRing G] [IsSimpleRing U] [Infinite k]

include D in
/-- **The left-handed affine same-divisor identity**, with the prescribed
source family `B + a H`, from the affine theorem in the opposite algebra. -/
theorem targetA_left_affine (hdim : ringKrullDim G < ⊤) (d a : U)
    (hd : d ≠ 0) (ha : a ≠ 0) (B : U) :
    ∃ H R S : U, 1 = R * d + S * d * (B + a * H) := by
  obtain ⟨H, R, S, h⟩ := D.op.targetA hdim (MulOpposite.op d) (MulOpposite.op a)
    (by simpa using hd) (by simpa using ha) (MulOpposite.op B)
  refine ⟨unop H, unop R, unop S, ?_⟩
  have := congrArg unop h
  simpa [unop_mul, mul_assoc] using this

include D in
/-- **The left-handed same-divisor identity** `1 = R d + S d F` in `U`,
from the affine theorem in the opposite algebra. -/
theorem targetA_left (hdim : ringKrullDim G < ⊤) (d : U) (hd : d ≠ 0) :
    ∃ F R S : U, 1 = R * d + S * d * F := by
  obtain ⟨H, R, S, h⟩ := D.op.targetA hdim (MulOpposite.op d) 1
    (by simpa using hd) one_ne_zero 0
  refine ⟨unop H, unop R, unop S, ?_⟩
  have := congrArg unop h
  simpa [unop_mul, mul_assoc] using this

end FilteredAlgebraData

end GeneralizedStafford
