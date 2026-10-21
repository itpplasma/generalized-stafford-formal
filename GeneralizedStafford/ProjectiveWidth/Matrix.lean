module

public import GeneralizedStafford.ProjectiveWidth.Theorem
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-! # Matrix statements with the original noncommutative multiplication order -/

namespace GeneralizedStafford.ProjectiveWidth

open MulOpposite
open scoped nonZeroDivisors

variable {A : Type*} [Ring A]

/-- Left matrix action on columns is right `A`-linear. -/
def matrixEnd {n : ℕ} : Matrix (Fin n) (Fin n) A →+*
    Module.End Aᵐᵒᵖ (Fin n → A) where
  toFun D :=
    { toFun := D.mulVec
      map_add' := Matrix.mulVec_add D
      map_smul' := fun r x => Matrix.mulVec_smul D r x }
  map_zero' := by apply LinearMap.ext; intro x; exact Matrix.zero_mulVec x
  map_one' := by apply LinearMap.ext; intro x; exact Matrix.one_mulVec x
  map_add' D E := by apply LinearMap.ext; intro x; exact Matrix.add_mulVec D E x
  map_mul' D E := by apply LinearMap.ext; intro x; exact (Matrix.mulVec_mulVec x D E).symm

/-- Every right-linear endomorphism of the free column module is a unique
matrix. This adapter is valid over noncommutative rings. -/
theorem matrixEnd_bijective (n : ℕ) : Function.Bijective (matrixEnd (A := A) (n := n)) := by
  classical
  constructor
  · intro D E h
    ext i j
    have he := congrFun (LinearMap.congr_fun h (Pi.single j 1)) i
    simpa only [matrixEnd, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec_single_one, Matrix.col_apply] using he
  · intro f
    let D : Matrix (Fin n) (Fin n) A := fun i j => f (Pi.single j 1) i
    refine ⟨D, ?_⟩
    apply LinearMap.ext
    intro x
    ext i
    have hx : (∑ j, op (x j) • (Pi.single j 1 : Fin n → A)) = x := by
      ext k
      simp [Pi.single_apply, Pi.smul_apply, apply_ite, MulOpposite.smul_eq_mul_unop]
    have he : D.mulVec x = f x := by
      calc
        D.mulVec x = ∑ j, op (x j) • f (Pi.single j 1) := by
          ext k
          simp [D, Matrix.mulVec, dotProduct, Pi.smul_apply,
            MulOpposite.smul_eq_mul_unop]
        _ = f (∑ j, op (x j) • (Pi.single j 1 : Fin n → A)) := by simp
        _ = f x := by rw [hx]
    exact congrFun he i

/-- Matrix/endomorphism identification preserving products, not reversing
them. Right-module scalars are represented by the opposite ring. -/
noncomputable def matrixEndEquiv (n : ℕ) :
    Matrix (Fin n) (Fin n) A ≃+* Module.End Aᵐᵒᵖ (Fin n → A) :=
  RingEquiv.ofBijective matrixEnd (matrixEnd_bijective n)

variable [IsDomain A] [OreLocalization.OreSet (Aᵐᵒᵖ)⁰]

/-- Matrix rank via the image of its action after Mathlib Ore localization. -/
noncomputable def matrixOreRank {n : ℕ} (d : Matrix (Fin n) (Fin n) A) : ℕ :=
  localizedImageRank (matrixEnd d)

/-- Conditional affine anchored width in `M_n(A)`, with `n/r+1` terms. -/
theorem matrix_anchored_width (hL : LeftOre A) (hS : S1 A) {n r : ℕ}
    (d a : Matrix (Fin n) (Fin n) A) (hd : matrixOreRank d = r) (hr : 0 < r)
    (ha : Function.Injective a.mulVec) (B : Fin (n / r) → Matrix (Fin n) (Fin n) A) :
    ∃ (H : Fin (n / r) → Matrix (Fin n) (Fin n) A)
      (U₀ : Matrix (Fin n) (Fin n) A) (U : Fin (n / r) → Matrix (Fin n) (Fin n) A),
      1 = d * U₀ + ∑ i, (B i + H i * a) * d * U i := by
  classical
  let e := matrixEndEquiv (A := A) n
  obtain ⟨H, U₀, U, h⟩ := free_anchored_width hL hS n r hr
    (matrixEnd d) (matrixEnd a) hd ha (fun i => matrixEnd (B i))
  refine ⟨fun i => e.symm (H i), e.symm U₀, fun i => e.symm (U i), ?_⟩
  apply e.injective
  simp only [map_one, map_add, map_mul, map_sum, RingEquiv.apply_symm_apply]
  exact h

/-- Rank two in `M_3(A)`: the full two-term affine identity. -/
theorem matrix_rank_two_three (hL : LeftOre A) (hS : S1 A)
    (d a B : Matrix (Fin 3) (Fin 3) A) (hd : matrixOreRank d = 2)
    (ha : Function.Injective a.mulVec) :
    ∃ H U₀ U₁ : Matrix (Fin 3) (Fin 3) A,
      1 = d * U₀ + (B + H * a) * d * U₁ := by
  obtain ⟨H, U₀, U, h⟩ := matrix_anchored_width hL hS d a hd (by omega) ha (fun _ => B)
  exact ⟨H 0, U₀, U 0, by simpa using h⟩

end GeneralizedStafford.ProjectiveWidth
