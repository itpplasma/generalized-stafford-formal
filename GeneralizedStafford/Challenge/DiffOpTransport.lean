import GeneralizedStafford.DifferentialOperators
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.Module.LinearMap.End

/-!
# Challenge transport: differential operators on a smooth affine variety

The definitions of the differential-operator section of `GeneralizedStaffordChallenge.lean`
(identical copy `Challenge.lean`) and the `GlobalStaffordChallenge` definitions of the Global Stafford statement are
restated verbatim below, in the same namespaces and under the same names, so that the solution
never imports the challenge. Each compared theorem `<name>` is proved here as `<name>_proof`;
`GeneralizedStaffordSolution.lean` restates it under its challenge name.

The bridge: `IsDifferentialOperator P` is membership of `P` in AlgebraicAnalysis' subalgebra
`DifferentialOperators.algebra` of finite-order operators (`isDifferentialOperator_iff`, by
induction on the order), and `diffOps k A` equals that subalgebra (`diffOps_eq_algebra`). The
ring-level statements of `GeneralizedStafford.DiffOp` are transported along this equality by
substitution, and the element-level statements by the membership equivalence.
-/

universe u v

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

/-! ## Bridge to AlgebraicAnalysis -/

section Bridge

/-- `IsOrderLE n P` is membership of `P` in the order-`n` filtration of
AlgebraicAnalysis (induction on `n`). -/
theorem isOrderLE_iff_mem_order {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    (n : ℕ) (P : Module.End k A) :
    GlobalStaffordChallenge.IsOrderLE n P ↔
      P ∈ AlgebraicAnalysis.DifferentialOperators.order (k := k) (R := A) n := by
  induction n generalizing P with
  | zero => exact (AlgebraicAnalysis.DifferentialOperators.mem_order_zero_iff P).symm
  | succ n ih =>
      rw [AlgebraicAnalysis.DifferentialOperators.mem_order_succ_iff]
      exact forall_congr' fun a => ih _

/-- `IsDifferentialOperator P` is membership of `P` in AlgebraicAnalysis' subalgebra
`DifferentialOperators.algebra` of finite-order operators. -/
theorem isDifferentialOperator_iff {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    (P : Module.End k A) :
    GlobalStaffordChallenge.IsDifferentialOperator P ↔
      P ∈ AlgebraicAnalysis.DifferentialOperators.algebra (k := k) (R := A) := by
  simp only [GlobalStaffordChallenge.IsDifferentialOperator,
    AlgebraicAnalysis.DifferentialOperators.mem_algebra_iff]
  exact exists_congr fun n => isOrderLE_iff_mem_order n P

/-- The challenge subalgebra `diffOps k A` is AlgebraicAnalysis' `DifferentialOperators.algebra`. -/
theorem diffOps_eq_algebra (k A : Type u) [Field k] [CommRing A] [Algebra k A] :
    diffOps k A = AlgebraicAnalysis.DifferentialOperators.algebra (k := k) (R := A) := by
  ext P
  exact isDifferentialOperator_iff P

end Bridge

/-! ## Transfer of the library results along `diffOps k A = DifferentialOperators.algebra`

Each lemma states a ring-level result for a subalgebra `S` with `S = DifferentialOperators.algebra`;
the substitution `S := DifferentialOperators.algebra` turns it into the library result. -/

section Transfer

theorem twoGeneratedRight_of_eq {k A : Type u} [Field k] [CharZero k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.Smooth k A]
    (S : Subalgebra k (Module.End k A))
    (h : S = AlgebraicAnalysis.DifferentialOperators.algebra (k := k) (R := A))
    (I : Submodule (↥S)ᵐᵒᵖ ↥S) :
    ∃ a b : ↥S, I = Submodule.span (↥S)ᵐᵒᵖ {a, b} := by
  subst h
  exact GeneralizedStafford.DiffOp.twoGeneratedRight k A I

theorem twoGeneratedLeft_of_eq {k A : Type u} [Field k] [CharZero k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.Smooth k A]
    (S : Subalgebra k (Module.End k A))
    (h : S = AlgebraicAnalysis.DifferentialOperators.algebra (k := k) (R := A))
    (I : Submodule ↥S ↥S) :
    ∃ a b : ↥S, I = Submodule.span ↥S {a, b} := by
  subst h
  exact GeneralizedStafford.DiffOp.twoGeneratedLeft k A I

theorem prescribedCyclicRight_of_eq {k A : Type u} [Field k] [CharZero k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.Smooth k A]
    (S : Subalgebra k (Module.End k A))
    (h : S = AlgebraicAnalysis.DifferentialOperators.algebra (k := k) (R := A))
    (M : Type v) [AddCommGroup M] [Module (↥S)ᵐᵒᵖ M] [Module.Finite (↥S)ᵐᵒᵖ M]
    (hM : ∀ m : M, ∃ s : ↥S, s ≠ 0 ∧ op s • m = 0)
    (x : M) (t : ↥S) (ht : t ≠ 0) :
    ∃ y : M, Submodule.span (↥S)ᵐᵒᵖ {x + op t • y} = ⊤ := by
  subst h
  exact GeneralizedStafford.DiffOp.prescribedCyclicRight k A M hM x t ht

theorem prescribedCyclicLeft_of_eq {k A : Type u} [Field k] [CharZero k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.Smooth k A]
    (S : Subalgebra k (Module.End k A))
    (h : S = AlgebraicAnalysis.DifferentialOperators.algebra (k := k) (R := A))
    (M : Type v) [AddCommGroup M] [Module ↥S M] [Module.Finite ↥S M]
    (hM : ∀ m : M, ∃ s : ↥S, s ≠ 0 ∧ s • m = 0)
    (x : M) (t : ↥S) (ht : t ≠ 0) :
    ∃ y : M, Submodule.span ↥S {x + t • y} = ⊤ := by
  subst h
  exact GeneralizedStafford.DiffOp.prescribedCyclicLeft k A M hM x t ht

end Transfer

/-! ## Proofs of the compared differential-operator statements -/

/-- Two generators for right ideals of `D_k(A)`. -/
theorem diffOpTwoGeneratedRight_proof : DiffOpTwoGeneratedRightStatement.{u} := by
  intro k _ _ A _ _ _ _ I
  exact twoGeneratedRight_of_eq (diffOps k A) (diffOps_eq_algebra k A) I

/-- Two generators for left ideals of `D_k(A)`. -/
theorem diffOpTwoGeneratedLeft_proof : DiffOpTwoGeneratedLeftStatement.{u} := by
  intro k _ _ A _ _ _ _ I
  exact twoGeneratedLeft_of_eq (diffOps k A) (diffOps_eq_algebra k A) I

/-- Theorem A for `D_k(A)`, right and left forms. -/
theorem diffOpFixedAnchor_proof : DiffOpFixedAnchorStatement.{u} := by
  intro k _ _ A _ _ _ _ d a B hd ha hB hd0 ha0
  obtain ⟨H, U, V, hH, hU, hV, h⟩ := GeneralizedStafford.DiffOp.affineForm_right k A d a B
    ((isDifferentialOperator_iff d).mp hd) hd0 ((isDifferentialOperator_iff a).mp ha) ha0
    ((isDifferentialOperator_iff B).mp hB)
  obtain ⟨H', U', V', hH', hU', hV', h'⟩ := GeneralizedStafford.DiffOp.affineForm_left k A d a B
    ((isDifferentialOperator_iff d).mp hd) hd0 ((isDifferentialOperator_iff a).mp ha) ha0
    ((isDifferentialOperator_iff B).mp hB)
  exact ⟨⟨H, U, V, (isDifferentialOperator_iff H).mpr hH, (isDifferentialOperator_iff U).mpr hU,
      (isDifferentialOperator_iff V).mpr hV, h⟩,
    ⟨H', U', V', (isDifferentialOperator_iff H').mpr hH', (isDifferentialOperator_iff U').mpr hU',
      (isDifferentialOperator_iff V').mpr hV', h'⟩⟩

/-- The Global Stafford identity for `D_k(A)`. -/
theorem diffOpGlobalStafford_proof : DiffOpGlobalStaffordStatement.{u} := by
  intro k _ _ A _ _ _ _ d hd hd0
  obtain ⟨F, R, S, hF, hR, hS, h⟩ :=
    GeneralizedStafford.DiffOp.globalStafford k A d ((isDifferentialOperator_iff d).mp hd) hd0
  exact ⟨F, R, S, (isDifferentialOperator_iff F).mpr hF, (isDifferentialOperator_iff R).mpr hR,
    (isDifferentialOperator_iff S).mpr hS, h⟩

/-- Finitely generated torsion right `D_k(A)`-modules are cyclic. -/
theorem diffOpCyclicRight_proof : DiffOpCyclicRightStatement.{u, v} := by
  intro k _ _ A _ _ _ _ M _ _ _ hM x t ht
  exact prescribedCyclicRight_of_eq (diffOps k A) (diffOps_eq_algebra k A) M hM x t ht

/-- Finitely generated torsion left `D_k(A)`-modules are cyclic. -/
theorem diffOpCyclicLeft_proof : DiffOpCyclicLeftStatement.{u, v} := by
  intro k _ _ A _ _ _ _ M _ _ _ hM x t ht
  exact prescribedCyclicLeft_of_eq (diffOps k A) (diffOps_eq_algebra k A) M hM x t ht

end GeneralizedStaffordChallenge
