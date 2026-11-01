module

public import GeneralizedStafford.FixedAnchor.Induction

@[expose] public section

/-!
# Theorem A' (fixed ideal) and Theorem A by specialization

This file formalizes `docs/core-theorem.md`, Sections 1 and 4 (frozen at
research revision `522b965`), for domains. A right ideal is a
`Submodule Rᵐᵒᵖ R`; `I ⊔ principalRightIdeal f` is `I + fR`.

The induction invariant `IdealBound I e` is the assertion `P(h)` of §4 with
`e = N - h + 1` written as the strict stratum `Small e` (`Small (e+1)` is
`DevLE e`). The step is the colon-free two-call descent of §4: the second
call uses offset `0`, tail `t*b` with `f*b ∈ I`, and the single canonical test
of `R/J`; the central pencil is the ordinary stability pencil of Lemma 3.6, and
the inclusion (4.2) uses invertibility of the nonzero central scalar.

Over a domain the regular elements are exactly the nonzero elements, so the
hypothesis "`I` contains a regular element" is `∃ s ∈ I, s ≠ 0`. The general
(zero-divisor) case is not formalized here.
-/

namespace GeneralizedStafford.FixedAnchor

open Module Module.Germ MulOpposite AlgebraicAnalysis
open AlgebraicAnalysis.ColonSupport AlgebraicAnalysis.DenominatorTorsion

universe u
variable {R : Type u} [Ring R]

/-- Epicity of the unit germ of `R/J` multiplied by `x` is smallness of
`R/(J + xR)` (Lemma 3.1, unit-germ form). -/
theorem smul_mkQ_epic_iff {e : ℕ} [IsNoetherian Rᵐᵒᵖ R]
    (J : Submodule Rᵐᵒᵖ R) (x : R) :
    Hom.Epic (op x • Hom.ofLinearMap (e := e) J.mkQ) ↔
      Module.Small Rᵐᵒᵖ e (R ⧸ (J ⊔ principalRightIdeal x)) := by
  rw [← quotient_section_epic_iff]
  have he : op x • Hom.ofLinearMap (e := e) J.mkQ =
      Hom.ofLinearMap (e := e) (J.mkQ.comp (leftMulLinear x)) := by
    change Hom.comp (Hom.ofLinearMap J.mkQ) (Hom.ofLinearMap (Section.leftMul x)) = _
    rw [← Hom.ofLinearMap_comp]
    rfl
  rw [he]

/-- A right ideal containing a nonzero element of a right Noetherian domain
has torsion quotient (I1 for domains). -/
theorem quotient_isTorsion_of_mem [IsDomain R] [IsNoetherian Rᵐᵒᵖ R]
    {I : Submodule Rᵐᵒᵖ R} {s : R} (hsI : s ∈ I) (hs : s ≠ 0) :
    IsTorsionRight (R := R) (M := R ⧸ I) := by
  refine quotient_isTorsion_of_principal_le
    (OreRightIntersection.rightOreCondition_of_isNoetherian (R := R)) s hs I ?_
  rintro y ⟨r, rfl⟩
  exact I.smul_mem (op r) hsI

/-- The torsion equation of §4 step 2: for every `f` there is a nonzero `b`
with `f*b ∈ I`. -/
theorem exists_mul_mem_of_mem [IsDomain R] [IsNoetherian Rᵐᵒᵖ R]
    {I : Submodule Rᵐᵒᵖ R} {s : R} (hsI : s ∈ I) (hs : s ≠ 0) (f : R) :
    ∃ b : R, b ≠ 0 ∧ f * b ∈ I := by
  obtain ⟨b, hb, hfb⟩ := quotient_isTorsion_of_mem hsI hs (I.mkQ f)
  refine ⟨b, hb, ?_⟩
  have h : I.mkQ (op b • f) = 0 := by rw [map_smul]; exact hfb
  exact (Submodule.Quotient.mk_eq_zero I).mp h

/-- The unit test of a quotient `R/J` with torsion quotient: offset `0`,
tail `1`. Satisfaction by `f` means that `R/(J + fR)` is small. -/
def unitTest [Nontrivial R] [IsNoetherian Rᵐᵒᵖ R] (J : Submodule Rᵐᵒᵖ R) (e : ℕ)
    (hJ : Module.DevLE Rᵐᵒᵖ e (R ⧸ J)) (hT : IsTorsionRight (R := R) (M := R ⧸ J)) :
    EpicGermTest R where
  level := e
  Target := R ⧸ J
  bounded := hJ
  torsion := hT
  q := Hom.ofLinearMap J.mkQ
  offset := 0
  epic := Hom.epic_ofLinearMap_of_surjective _ (Submodule.mkQ_surjective _)
  tail := 1
  tail_ne := one_ne_zero

/-- The fixed-ideal induction invariant `P(h)` of §4, with the strict stratum
`Small e`. It carries every finite family of actual epic germ tests. -/
def IdealBound (I : Submodule Rᵐᵒᵖ R) (e : ℕ) : Prop :=
  ∀ (x t : R), t ≠ 0 → ∀ {ι : Type u} [Fintype ι] (tests : ι → EpicGermTest R),
    ∃ H : R, Module.Small Rᵐᵒᵖ e (R ⧸ (I ⊔ principalRightIdeal (x + H * t))) ∧
      ∀ i, (tests i).Satisfied (x + H * t)

/-- The inclusion (4.2): if `f*b ∈ I` and `lam` is a unit commuting with
everything, then `g*b ∈ I + (f + lam*g)R`. -/
theorem mul_mem_pencil {I : Submodule Rᵐᵒᵖ R} {f g b lam : R}
    (hfb : f * b ∈ I) (hlam : ∀ x : R, lam * x = x * lam) (hu : IsUnit lam) :
    g * b ∈ I ⊔ principalRightIdeal (f + lam * g) := by
  obtain ⟨u, rfl⟩ := hu
  have h1 : (f + ↑u * g) * b ∈ I ⊔ principalRightIdeal (f + ↑u * g) :=
    Submodule.mem_sup_right ⟨b, rfl⟩
  have h2 : g * b * ↑u = (f + ↑u * g) * b - f * b := by
    rw [add_mul, mul_assoc (↑u : R) g b, hlam (g * b)]; abel
  have h3 : g * b * ↑u ∈ I ⊔ principalRightIdeal (f + ↑u * g) := by
    rw [h2]; exact Submodule.sub_mem _ h1 (Submodule.mem_sup_left hfb)
  have h4 := Submodule.smul_mem _ (op (↑u⁻¹ : R)) h3
  have h5 : op (↑u⁻¹ : R) • (g * b * ↑u) = g * b := by
    change g * b * ↑u * ↑u⁻¹ = g * b
    rw [mul_assoc, Units.mul_inv, mul_one]
  rwa [h5] at h4

variable [IsDomain R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
variable {k : Type*} [Field k] [Infinite k] [Algebra k R]

include k in
/-- Base `P(0)`: source selection (Lemma 3.6) with the bound inherited from
`R/I`. -/
theorem idealBound_initial {I : Submodule Rᵐᵒᵖ R} {N : ℕ}
    (hI : Module.DevLE Rᵐᵒᵖ N (R ⧸ I)) : IdealBound I (N + 1) := by
  intro x t ht ι _ tests
  obtain ⟨H, hH⟩ := exists_affine_epic_tests (k := k)
    (fun i => (tests i).level) (fun i => (tests i).Target)
    (fun i => (tests i).bounded) (fun i => (tests i).torsion)
    (fun i => (tests i).q) (fun i => (tests i).offset) (fun i => (tests i).epic)
    (fun i => (tests i).tail) (fun i => (tests i).tail_ne) ht x
  exact ⟨H, hI.of_surjective (Submodule.factor le_sup_left)
    (Submodule.factor_surjective le_sup_left), hH⟩

omit [IsSimpleRing R] in
include k in
/-- The two-call step `P(h) → P(h+1)` of §4, lowering `Small (e+1)` to
`Small e` for the fixed ideal `I`, preserving every old test. -/
theorem idealBound_step {I : Submodule Rᵐᵒᵖ R} {s : R} (hsI : s ∈ I) (hs : s ≠ 0)
    (e : ℕ) (hbound : IdealBound I (e + 1)) : IdealBound I e := by
  classical
  intro x t ht ι _ tests
  -- First call.
  obtain ⟨H, hJ, htests⟩ := hbound x t ht tests
  set f := x + H * t with hf
  set J := I ⊔ principalRightIdeal f with hJdef
  have hTJ : IsTorsionRight (R := R) (M := R ⧸ J) :=
    quotient_isTorsion_of_mem (Submodule.mem_sup_left hsI) hs
  -- Torsion equation.
  obtain ⟨b, hb, hfb⟩ := exists_mul_mem_of_mem hsI hs f
  -- Second call: offset 0, tail t*b, the single unit test of R/J.
  obtain ⟨H₂, hQ, htest⟩ := hbound 0 (t * b) (mul_ne_zero ht hb)
    (fun _ : PUnit.{u + 1} => unitTest J e hJ hTJ)
  set g := H₂ * t with hg
  have hgb : (0 : R) + H₂ * (t * b) = g * b := by rw [zero_add, hg, mul_assoc]
  rw [hgb] at hQ
  set Q := I ⊔ principalRightIdeal (g * b) with hQdef
  have htJ : Module.Small Rᵐᵒᵖ e (R ⧸ (J ⊔ principalRightIdeal (g * b))) := by
    have h := htest PUnit.unit
    change Hom.Epic (e := e) (0 + op (((0 : R) + H₂ * (t * b)) * 1) •
      Hom.ofLinearMap J.mkQ) at h
    rw [zero_add, hgb, mul_one] at h
    exact (smul_mkQ_epic_iff J (g * b)).mp h
  -- Vanishing of the joint top: the germ `v = q_Q f` is epic.
  have hjoint : J ⊔ principalRightIdeal (g * b) = Q ⊔ principalRightIdeal f := by
    rw [hJdef, hQdef, sup_assoc, sup_assoc, sup_comm (principalRightIdeal f)]
  rw [hjoint] at htJ
  have hv : Hom.Epic (op f • Hom.ofLinearMap (e := e) Q.mkQ) :=
    (smul_mkQ_epic_iff Q f).mpr htJ
  -- Good central scalar.
  let F := Classical.choice hQ.nonempty_criticalFiltration
  have hbad := germ_pencil_finite (k := k) hQ F
    (op f • Hom.ofLinearMap (e := e) Q.mkQ) (op g • Hom.ofLinearMap (e := e) Q.mkQ) hv
  have hold : (⋃ i, {c : k | ¬ (tests i).Satisfied (f + algebraMap k R c * g)}).Finite :=
    Set.finite_iUnion fun i => (tests i).pencil_finite (htests i) g
  obtain ⟨c, hc⟩ := ((hbad.union hold).union (Set.finite_singleton (0 : k))).exists_notMem
  have hc0 : c ≠ 0 := fun h => hc (Set.mem_union_right _ h)
  set lam := algebraMap k R c with hlamdef
  have hlam : ∀ y : R, lam * y = y * lam := fun y => Algebra.commutes c y
  have hunit : IsUnit lam := (IsUnit.mk0 c hc0).map (algebraMap k R)
  have hep : Hom.Epic (op f • Hom.ofLinearMap (e := e) Q.mkQ +
      op lam • (op g • Hom.ofLinearMap (e := e) Q.mkQ)) := by
    by_contra hn
    exact hc (Set.mem_union_left _ (Set.mem_union_left _ hn))
  have hkeep : ∀ i, (tests i).Satisfied (f + lam * g) := by
    intro i
    by_contra hn
    exact hc (Set.mem_union_left _ (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨i, hn⟩)))
  -- Drop: `q_Q (f + lam g)` is epic, and `Q ≤ J'`.
  have hep' : Hom.Epic (op (f + lam * g) • Hom.ofLinearMap (e := e) Q.mkQ) := by
    have hid := test_pencil_identity (Hom.ofLinearMap (e := e) Q.mkQ) 0 f g 1 lam hlam
    simp only [mul_one, zero_add] at hid
    rwa [hid]
  have hsmall := (smul_mkQ_epic_iff Q (f + lam * g)).mp hep'
  have hideal : Q ⊔ principalRightIdeal (f + lam * g) =
      I ⊔ principalRightIdeal (f + lam * g) := by
    apply le_antisymm
    · refine sup_le (sup_le le_sup_left ?_) le_sup_right
      rintro y ⟨r, rfl⟩
      exact Submodule.smul_mem _ (op r) (mul_mem_pencil hfb hlam hunit)
    · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  rw [hideal] at hsmall
  -- Affine form.
  have heq : f + lam * g = x + (H + lam * H₂) * t := affine_update x H H₂ t lam
  rw [heq] at hsmall hkeep
  exact ⟨H + lam * H₂, hsmall, hkeep⟩

omit [IsSimpleRing R] in
include k in
/-- Finite descent from `P(0)` to `P(N+1)`. -/
theorem idealBound_descend {I : Submodule Rᵐᵒᵖ R} {s : R} (hsI : s ∈ I) (hs : s ≠ 0)
    (e h : ℕ) : IdealBound I (e + h) → IdealBound I e := by
  induction h with
  | zero => exact fun hb => hb
  | succ h ih =>
    intro hb
    exact ih (idealBound_step (k := k) hsI hs (e + h) hb)

include k in
/-- **Theorem A' with tests.** For a simple right Noetherian domain with an
infinite central field and a right ideal `I` containing a nonzero element with
`R/I` of finite deviation, every `x`, `t ≠ 0` and every finite family of actual
epic germ tests admit `H` with `I + (x + H t)R = R` and all tests satisfied. -/
theorem fixed_ideal_with_tests {I : Submodule Rᵐᵒᵖ R} (hreg : ∃ s ∈ I, s ≠ 0)
    {N : ℕ} (hdev : Module.DevLE Rᵐᵒᵖ N (R ⧸ I)) (x : R) {t : R} (ht : t ≠ 0)
    {ι : Type u} [Fintype ι] (tests : ι → EpicGermTest R) :
    ∃ H : R, I ⊔ principalRightIdeal (x + H * t) = ⊤ ∧
      ∀ i, (tests i).Satisfied (x + H * t) := by
  obtain ⟨s, hsI, hs⟩ := hreg
  have hzero := idealBound_descend (k := k) hsI hs 0 (N + 1)
    (by simpa only [Nat.zero_add] using idealBound_initial (k := k) hdev)
  obtain ⟨H, hsmall, htests⟩ := hzero x t ht tests
  refine ⟨H, ?_, htests⟩
  have hz : (I ⊔ principalRightIdeal (x + H * t)).mkQ 1 = 0 := hsmall.elim _ _
  have h1 : (1 : R) ∈ I ⊔ principalRightIdeal (x + H * t) :=
    (Submodule.Quotient.mk_eq_zero _).mp hz
  refine eq_top_iff.mpr fun y _ => ?_
  have hy := Submodule.smul_mem _ (op y) h1
  rwa [op_smul_eq_mul, one_mul] at hy

include k in
/-- **Theorem A' (fixed ideal)**, `docs/core-theorem.md` §1, for domains:
`I + (x + H t)R = R`. -/
theorem fixed_ideal {I : Submodule Rᵐᵒᵖ R} (hreg : ∃ s ∈ I, s ≠ 0)
    {N : ℕ} (hdev : Module.DevLE Rᵐᵒᵖ N (R ⧸ I)) (x : R) {t : R} (ht : t ≠ 0) :
    ∃ H : R, I ⊔ principalRightIdeal (x + H * t) = ⊤ := by
  obtain ⟨H, hH, _⟩ := fixed_ideal_with_tests (k := k) hreg hdev x ht
    (fun i : PEmpty.{u + 1} => nomatch i)
  exact ⟨H, hH⟩

include k in
/-- **Theorem A (fixed anchor) from Theorem A'**, exactly as in §1:
`I = dR`, `x = B d`, `t = a d`. -/
theorem fixed_anchor_of_fixed_ideal {N : ℕ} {d a : R} (hd : d ≠ 0) (ha : a ≠ 0)
    (hdev : Module.DevLE Rᵐᵒᵖ N (R ⧸ anchor d)) (B : R) :
    ∃ H U V : R, 1 = d * U + (B + H * a) * d * V := by
  obtain ⟨H, hH⟩ := fixed_ideal (k := k) (I := anchor d) ⟨d, ⟨1, mul_one d⟩, hd⟩ hdev
    (B * d) (mul_ne_zero ha hd)
  have h1 : (1 : R) ∈ anchor d ⊔ principalRightIdeal (B * d + H * (a * d)) := by
    rw [hH]; exact Submodule.mem_top
  obtain ⟨y, ⟨U, rfl⟩, z, ⟨V, rfl⟩, he⟩ := Submodule.mem_sup.mp h1
  refine ⟨H, U, V, ?_⟩
  rw [← he]
  change d * U + (B * d + H * (a * d)) * V = d * U + (B + H * a) * d * V
  simp only [add_mul, mul_assoc]

end GeneralizedStafford.FixedAnchor

namespace GeneralizedStafford.FixedAnchor

open Module MulOpposite AlgebraicAnalysis
open AlgebraicAnalysis.ColonSupport AlgebraicAnalysis.DenominatorTorsion

universe u v
variable {R : Type u} [Ring R] [IsDomain R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
variable {k : Type*} [Field k] [Infinite k] [Algebra k R]

/-! ## Corollary B: the omega bound supplies (Fin_I) -/

omit [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R] in
/-- **Corollary B (ideals)**, Lemma 6.1: under `Kdim R ≤ ω` every right
ideal containing a nonzero element has finite-deviation quotient. -/
theorem quotient_finite_of_omega (hR : Module.DevLEOmega Rᵐᵒᵖ R)
    {I : Submodule Rᵐᵒᵖ R} (hreg : ∃ s ∈ I, s ≠ 0) :
    ∃ N, Module.DevLE Rᵐᵒᵖ N (R ⧸ I) := by
  obtain ⟨s, hsI, hs⟩ := hreg
  obtain ⟨N, hN⟩ := principal_quotient_finite_of_omega hR hs
  refine ⟨N, quotient_devLE hN I ?_⟩
  rintro y ⟨r, rfl⟩
  exact I.smul_mem (op r) hsI

include k in
/-- **Theorem A' under `Kdim R ≤ ω`** (Corollary B). -/
theorem fixed_ideal_of_devLE_omega (hR : Module.DevLEOmega Rᵐᵒᵖ R)
    {I : Submodule Rᵐᵒᵖ R} (hreg : ∃ s ∈ I, s ≠ 0) (x : R) {t : R} (ht : t ≠ 0) :
    ∃ H : R, I ⊔ principalRightIdeal (x + H * t) = ⊤ := by
  obtain ⟨N, hN⟩ := quotient_finite_of_omega hR hreg
  exact fixed_ideal (k := k) hreg hN x ht

/-! ## Corollary C.1: prescribed affine cyclicity of torsion modules -/

section Modules

variable {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]

omit [IsDomain R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R] in
/-- The cyclic map `r ↦ u r` of a right module. -/
def cyclicMap (u : M) : R →ₗ[Rᵐᵒᵖ] M where
  toFun r := op r • u
  map_add' r s := by rw [op_add, add_smul]
  map_smul' a r := by
    change op (r * unop a) • u = a • (op r • u)
    rw [op_mul, op_unop, mul_smul]

omit [IsDomain R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R] in
theorem range_cyclicMap (u : M) :
    LinearMap.range (cyclicMap (R := R) u) = Submodule.span Rᵐᵒᵖ {u} := by
  ext m
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩; exact ⟨op r, rfl⟩
  · rintro ⟨a, rfl⟩; exact ⟨unop a, by change op (unop a) • u = a • u; rw [op_unop]⟩

omit [IsDomain R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R] in
/-- A cyclic submodule of a module of deviation `≤ N` is `R/ann(u)` with the
same bound. -/
theorem devLE_cyclic {N : ℕ} (hM : Module.DevLE Rᵐᵒᵖ N M) (u : M) :
    Module.DevLE Rᵐᵒᵖ N (R ⧸ LinearMap.ker (cyclicMap (R := R) u)) :=
  (Module.devLE_linearEquiv_iff N (cyclicMap (R := R) u).quotKerEquivRange).mpr
    (hM.of_injective (LinearMap.range (cyclicMap (R := R) u)).subtype
      Subtype.val_injective)

include k in
/-- The induction of Lemma 6.2 over a finite generating set, relative to an
arbitrary submodule `W`. Only (Fin_I) for the cyclic annihilators is used. -/
theorem prescribed_cyclic_aux
    (hcyc : ∀ u : M, ∃ N, Module.DevLE Rᵐᵒᵖ N (R ⧸ LinearMap.ker (cyclicMap (R := R) u)))
    (htor : IsTorsionRight (R := R) (M := M)) {t : R} (ht : t ≠ 0) (s : Finset M) :
    ∀ W : Submodule Rᵐᵒᵖ M, Submodule.span Rᵐᵒᵖ (s : Set M) ⊔ W = ⊤ →
      ∀ x : M, ∃ h : M, Submodule.span Rᵐᵒᵖ {x + op t • h} ⊔ W = ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro W hW x
    refine ⟨0, ?_⟩
    rw [Finset.coe_empty, Submodule.span_empty, bot_sup_eq] at hW
    rw [hW, sup_top_eq]
  | insert u s _ ih =>
    intro W hW x
    have hW' : Submodule.span Rᵐᵒᵖ (s : Set M) ⊔ (W ⊔ Submodule.span Rᵐᵒᵖ {u}) = ⊤ := by
      rw [Finset.coe_insert, Submodule.span_insert] at hW
      rw [← hW]
      ac_rfl
    obtain ⟨y, hy⟩ := ih (W ⊔ Submodule.span Rᵐᵒᵖ {u}) hW' x
    set c := x + op t • y with hc
    obtain ⟨b, hb, hcb⟩ := htor c
    obtain ⟨N, hN⟩ := hcyc u
    obtain ⟨s₀, hs₀, hs₀u⟩ := htor u
    have hreg : ∃ s ∈ LinearMap.ker (cyclicMap (R := R) u), s ≠ 0 := ⟨s₀, hs₀u, hs₀⟩
    obtain ⟨H, hH⟩ := fixed_ideal (k := k) hreg hN 0 (mul_ne_zero ht hb)
    rw [zero_add] at hH
    have h1 : (1 : R) ∈ LinearMap.ker (cyclicMap (R := R) u) ⊔
        principalRightIdeal (H * (t * b)) := by rw [hH]; exact Submodule.mem_top
    obtain ⟨i, hi, w, ⟨r, rfl⟩, hiw⟩ := Submodule.mem_sup.mp h1
    set kk := op H • u with hkk
    set z := c + op t • kk with hz
    -- `u = (u H t b) r` and `z b = (u H) t b`.
    have hu : u = op r • (op b • z) := by
      have h := congrArg (cyclicMap (R := R) u) hiw
      change op (i + H * (t * b) * r : R) • u = op (1 : R) • u at h
      rw [op_one, one_smul, op_add, add_smul] at h
      change cyclicMap (R := R) u i + _ = u at h
      rw [LinearMap.mem_ker.mp hi, zero_add] at h
      rw [hz, smul_add, hcb, zero_add, ← h, hkk]
      simp only [op_mul, mul_smul]
    have huz : u ∈ Submodule.span Rᵐᵒᵖ {z} := by
      rw [hu]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z))
    have hspan_u : Submodule.span Rᵐᵒᵖ {u} ≤ Submodule.span Rᵐᵒᵖ {z} :=
      (Submodule.span_singleton_le_iff_mem _ _).mpr huz
    have hcz : c ∈ Submodule.span Rᵐᵒᵖ {z} := by
      have hk : op t • kk ∈ Submodule.span Rᵐᵒᵖ {z} :=
        hspan_u (Submodule.smul_mem _ _ (Submodule.smul_mem _ _
          (Submodule.mem_span_singleton_self u)))
      have : c = z - op t • kk := by rw [hz, add_sub_cancel_right]
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_span_singleton_self z) hk
    refine ⟨y + kk, ?_⟩
    have hzx : x + op t • (y + kk) = z := by rw [hz, hc, smul_add, add_assoc]
    rw [hzx]
    refine eq_top_iff.mpr ?_
    rw [← hy]
    refine sup_le ?_ (sup_le le_sup_right (hspan_u.trans le_sup_left))
    exact ((Submodule.span_singleton_le_iff_mem _ _).mpr hcz).trans le_sup_left

include k in
/-- Lemma 6.2 under (Fin_I) for all cyclic annihilators. -/
theorem prescribed_cyclic_of_cyclic [Module.Finite Rᵐᵒᵖ M]
    (hcyc : ∀ u : M, ∃ N, Module.DevLE Rᵐᵒᵖ N (R ⧸ LinearMap.ker (cyclicMap (R := R) u)))
    (htor : IsTorsionRight (R := R) (M := M)) (x : M) {t : R} (ht : t ≠ 0) :
    ∃ h : M, Submodule.span Rᵐᵒᵖ {x + op t • h} = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Rᵐᵒᵖ) (M := M)
  obtain ⟨h, hh⟩ := prescribed_cyclic_aux (k := k) hcyc htor ht s ⊥
    (by rw [hs, top_sup_eq]) x
  exact ⟨h, by rwa [sup_bot_eq] at hh⟩

include k in
/-- **Corollary C.1**, Lemma 6.2, for domains: a finitely generated torsion
right module of finite deviation is cyclic with prescribed affine generator
`x + h t`, for every `x` and every `t ≠ 0`. -/
theorem prescribed_cyclic [Module.Finite Rᵐᵒᵖ M]
    (htor : IsTorsionRight (R := R) (M := M)) {N : ℕ} (hM : Module.DevLE Rᵐᵒᵖ N M)
    (x : M) {t : R} (ht : t ≠ 0) :
    ∃ h : M, Submodule.span Rᵐᵒᵖ {x + op t • h} = ⊤ :=
  prescribed_cyclic_of_cyclic (k := k) (fun u => ⟨N, devLE_cyclic hM u⟩) htor x ht

include k in
/-- **Corollary C.1 under (H_all)**: if every principal quotient `R/dR`
(`d ≠ 0`) has finite deviation, the dimension hypothesis is automatic. -/
theorem prescribed_cyclic_of_principal [Module.Finite Rᵐᵒᵖ M]
    (hall : ∀ d : R, d ≠ 0 → ∃ N, Module.DevLE Rᵐᵒᵖ N (R ⧸ anchor d))
    (htor : IsTorsionRight (R := R) (M := M)) (x : M) {t : R} (ht : t ≠ 0) :
    ∃ h : M, Submodule.span Rᵐᵒᵖ {x + op t • h} = ⊤ := by
  refine prescribed_cyclic_of_cyclic (k := k) (fun u => ?_) htor x ht
  obtain ⟨s, hs, hsu⟩ := htor u
  obtain ⟨N, hN⟩ := hall s hs
  refine ⟨N, quotient_devLE hN _ ?_⟩
  rintro y ⟨r, rfl⟩
  exact (LinearMap.ker (cyclicMap (R := R) u)).smul_mem (op r) hsu

include k in
/-- **Corollary C.1 under `Kdim R ≤ ω`.** -/
theorem prescribed_cyclic_of_devLE_omega [Module.Finite Rᵐᵒᵖ M]
    (hR : Module.DevLEOmega Rᵐᵒᵖ R)
    (htor : IsTorsionRight (R := R) (M := M)) (x : M) {t : R} (ht : t ≠ 0) :
    ∃ h : M, Submodule.span Rᵐᵒᵖ {x + op t • h} = ⊤ :=
  prescribed_cyclic_of_principal (k := k)
    (fun _ hd => principal_quotient_finite_of_omega hR hd) htor x ht

/-! ## Corollary C.2: two-generated right ideals (domains) -/

omit [IsSimpleRing R] in
/-- For `a ≠ 0` in `I`, the quotient `I/aR` is torsion (right Ore condition). -/
theorem ideal_quotient_isTorsion {I : Submodule Rᵐᵒᵖ R} {a : R} (ha : a ≠ 0) :
    IsTorsionRight (R := R)
      (M := ↥I ⧸ (principalRightIdeal a).comap I.subtype) := by
  intro z
  obtain ⟨⟨m, hm⟩, rfl⟩ := Submodule.mkQ_surjective _ z
  by_cases hm0 : m = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    rw [op_one, one_smul]
    have : (⟨m, hm⟩ : ↥I) = 0 := Subtype.ext hm0
    rw [this, map_zero]
  obtain ⟨x, y', hxy, hne⟩ :=
    OreRightIntersection.rightOreCondition_of_isNoetherian (R := R) ha hm0
  have hy' : y' ≠ 0 := by rintro rfl; rw [mul_zero] at hxy; exact hne hxy
  refine ⟨y', hy', ?_⟩
  rw [← map_smul]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨x, hxy.trans rfl⟩

include k in
/-- **Corollary C.2** (Lemma 6.3) for domains, under (H_all): if `a ≠ 0` lies
in the right ideal `I` (for a domain and `I ≠ 0` this is `aQ = IQ`), then for
every `y ∈ I` and `t ≠ 0` some `h ∈ I` gives `I = aR + (y + h t)R`. -/
theorem two_generated_of_principal
    (hall : ∀ d : R, d ≠ 0 → ∃ N, Module.DevLE Rᵐᵒᵖ N (R ⧸ anchor d))
    {I : Submodule Rᵐᵒᵖ R} {a : R} (haI : a ∈ I) (ha : a ≠ 0)
    {y : R} (hyI : y ∈ I) {t : R} (ht : t ≠ 0) :
    ∃ h ∈ I, I = principalRightIdeal a ⊔ principalRightIdeal (y + h * t) := by
  classical
  set K := (principalRightIdeal a).comap I.subtype
  obtain ⟨hbar, hh⟩ := prescribed_cyclic_of_principal (k := k) (M := ↥I ⧸ K) hall
    (ideal_quotient_isTorsion ha) (K.mkQ ⟨y, hyI⟩) ht
  obtain ⟨⟨h, hhI⟩, rfl⟩ := Submodule.mkQ_surjective K hbar
  refine ⟨h, hhI, le_antisymm ?_ ?_⟩
  · intro m hm
    have hmem : K.mkQ ⟨m, hm⟩ ∈ Submodule.span Rᵐᵒᵖ
        {K.mkQ ⟨y, hyI⟩ + op t • K.mkQ ⟨h, hhI⟩} := by rw [hh]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    rw [← map_smul, ← map_add, ← map_smul] at hc
    have hK : c • ((⟨y, hyI⟩ : ↥I) + op t • ⟨h, hhI⟩) - ⟨m, hm⟩ ∈ K :=
      (Submodule.Quotient.eq K).mp hc
    obtain ⟨r, hr⟩ := hK
    have hr' : a * r = (y + h * t) * unop c - m := by
      have := hr
      change a * r = ((y + h * t) * unop c) - m at this
      exact this
    have : m = a * (-r) + (y + h * t) * unop c := by
      rw [mul_neg, hr']; abel
    rw [this]
    exact Submodule.add_mem_sup ⟨-r, rfl⟩ ⟨unop c, rfl⟩
  · refine sup_le ?_ ?_
    · rintro z ⟨r, rfl⟩; exact I.smul_mem (op r) haI
    · rintro z ⟨r, rfl⟩
      exact I.smul_mem (op r) (I.add_mem hyI (I.smul_mem (op t) hhI))

include k in
/-- **Corollary C.2 under `Kdim R ≤ ω`.** -/
theorem two_generated_of_devLE_omega (hR : Module.DevLEOmega Rᵐᵒᵖ R)
    {I : Submodule Rᵐᵒᵖ R} {a : R} (haI : a ∈ I) (ha : a ≠ 0)
    {y : R} (hyI : y ∈ I) {t : R} (ht : t ≠ 0) :
    ∃ h ∈ I, I = principalRightIdeal a ⊔ principalRightIdeal (y + h * t) :=
  two_generated_of_principal (k := k)
    (fun _ hd => principal_quotient_finite_of_omega hR hd) haI ha hyI ht

include k in
/-- Every right ideal is two-generated under (H_all). -/
theorem exists_two_generators_of_principal
    (hall : ∀ d : R, d ≠ 0 → ∃ N, Module.DevLE Rᵐᵒᵖ N (R ⧸ anchor d))
    (I : Submodule Rᵐᵒᵖ R) :
    ∃ a b : R, I = principalRightIdeal a ⊔ principalRightIdeal b := by
  by_cases hI : ∃ a ∈ I, a ≠ 0
  · obtain ⟨a, haI, ha⟩ := hI
    obtain ⟨h, _, hh⟩ := two_generated_of_principal (k := k) hall haI ha I.zero_mem one_ne_zero
    exact ⟨a, 0 + h * 1, hh⟩
  · simp only [not_exists, not_and, not_not] at hI
    refine ⟨0, 0, ?_⟩
    have hbot : I = ⊥ := (Submodule.eq_bot_iff I).mpr hI
    have h0 : principalRightIdeal (0 : R) = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr ?_
      rintro z ⟨r, rfl⟩; exact zero_mul r
    rw [hbot, h0, sup_bot_eq]

end Modules

end GeneralizedStafford.FixedAnchor
