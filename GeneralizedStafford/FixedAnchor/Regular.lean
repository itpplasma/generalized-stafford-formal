module

public import GeneralizedStafford.Goldie.Torsion
public import GeneralizedStafford.FixedAnchor.FixedIdeal

@[expose] public section

/-!
# Theorem A', Theorem A and Corollaries B, C.1, C.2 without the domain hypothesis

This file formalizes `docs/core-theorem.md` (frozen at research revision
`522b965`), Sections 1, 3, 4 and Lemmas 6.1–6.3, for simple right Noetherian
rings with an infinite central field. Zero divisors are allowed:

* anchors `d`, the element witnessing (Reg_I), and test tails are **regular**
  (`∈ R⁰`, two-sided non-zero-divisors, convention C2);
* the affine tails `t` and `a` are only required to be nonzero;
* torsion is Goldie torsion (`IsGoldieTorsion`, convention C4).

Input I1 (Goldie's theorem) is proved in `GeneralizedStafford.Goldie`, so no
Ore hypothesis appears. The descent is literally the two-call descent of §4,
as in the domain file `FixedIdeal.lean`; only the torsion inputs and the
regularity of tails change.

Corollary C.2 is stated with the hypothesis "`I/aR` is Goldie-torsion", i.e.
every `y ∈ I` has a regular `s` with `y s ∈ aR`. This is the elementwise
content of `aQ = IQ` used in Lemma 6.3; the existence of such an `a` (via
Wedderburn–Artin for the classical quotient ring `Q`) is not formalized, so
"every right ideal is two-generated" is formalized only for domains.
-/

namespace GeneralizedStafford.FixedAnchor.Regular

open Module Module.Germ MulOpposite nonZeroDivisors AlgebraicAnalysis
open AlgebraicAnalysis.ColonSupport AlgebraicAnalysis.DenominatorTorsion
open AlgebraicAnalysis.Goldie GeneralizedStafford.Goldie

universe u v

/-! ## Source selection for Goldie-torsion germ tests (Lemma 3.6) -/

section Selection

variable {R : Type u} [Ring R]

/-- Simultaneous finite critical germ tests with prescribed affine tail, for
Goldie-torsion critical duals and regular test tails. -/
theorem exists_affine_germ_tests
    [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    {k : Type*} [Field k] [Infinite k] [Algebra k R]
    {ι : Type*} [Fintype ι] (e : ι → ℕ) (M C : ι → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module Rᵐᵒᵖ (M i)]
    [∀ i, IsNoetherian Rᵐᵒᵖ (M i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module Rᵐᵒᵖ (C i)]
    [∀ i, IsNoetherian Rᵐᵒᵖ (C i)]
    (hM : ∀ i, Module.DevLE Rᵐᵒᵖ (e i) (M i))
    (hC : ∀ i, Module.Critical Rᵐᵒᵖ (e i) (C i))
    (ht : ∀ i, IsGoldieTorsion R (C i))
    (q z : ∀ i, Hom Rᵐᵒᵖ (e i) R (M i)) (hq : ∀ i, Hom.Epic (q i))
    (b : ι → R) (hb : ∀ i, b i ∈ R⁰) {a : R} (ha : a ≠ 0) (B : R) :
    ∃ H : R, ∀ i, Function.Injective
      (fun h : Hom Rᵐᵒᵖ (e i) (M i) (C i) =>
        Hom.comp h (z i + op ((B + H * a) * b i) • q i)) := by
  classical
  let : ∀ i, DivisionRing (End Rᵐᵒᵖ (e i) (C i)) := fun i => End.divisionRing (hC i)
  let : ∀ i, Module.Finite (End Rᵐᵒᵖ (e i) (C i))
      (Hom Rᵐᵒᵖ (e i) (M i) (C i)) := fun i => Hom.finite_of_devLE (hM i) (hC i)
  let κ (i : ι) : k →+* End Rᵐᵒᵖ (e i) (C i) :=
    End.centralMap.comp (oppositeCentralField (R := R) k)
  let P (i : ι) := Hom.precompLinear (C := C i) (q i)
  let Z (i : ι) := Hom.precompLinear (C := C i) (z i)
  obtain ⟨H, hH⟩ := exists_affine_source_of_goldie
    (fun i => isGoldieTorsion_section (hC i) (ht i))
    (algebraMap k R) κ
    (fun i c x => (End.centralMap_commute (oppositeCentralField (R := R) k c) x).eq)
    (fun i c w => section_central_scalar (oppositeCentralField (R := R) k c) w)
    P Z (fun i => (hq i).right_cancel)
    Finset.univ b (fun i _ => hb i) ha B
  refine ⟨H, fun i => ?_⟩
  have hi := hH i (Finset.mem_univ i)
  convert hi using 1
  funext h
  exact Hom.comp_add h (z i) (op ((B + H * a) * b i) • q i) |>.trans
    (congrArg (Hom.comp h (z i) + ·)
      (Hom.comp_assoc h (q i) (Hom.ofLinearMap (Section.leftMul _))).symm)

/-- Finite affine selection for epic germ tests with Goldie-torsion targets
and regular test tails (Lemma 3.6, selection part). -/
theorem exists_affine_epic_tests
    [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    {k : Type*} [Field k] [Infinite k] [Algebra k R]
    {ι : Type*} [Fintype ι] (e : ι → ℕ) (M : ι → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module Rᵐᵒᵖ (M i)]
    [∀ i, IsNoetherian Rᵐᵒᵖ (M i)]
    (hM : ∀ i, Module.DevLE Rᵐᵒᵖ (e i) (M i))
    (ht : ∀ i, IsGoldieTorsion R (M i))
    (q z : ∀ i, Hom Rᵐᵒᵖ (e i) R (M i)) (hq : ∀ i, Hom.Epic (q i))
    (b : ι → R) (hb : ∀ i, b i ∈ R⁰) {a : R} (ha : a ≠ 0) (B : R) :
    ∃ H : R, ∀ i, Hom.Epic (z i + op ((B + H * a) * b i) • q i) := by
  classical
  let F (i : ι) : Module.CriticalFiltration Rᵐᵒᵖ (e i) (M i) :=
    Classical.choice (hM i).nonempty_criticalFiltration
  let J := (i : ι) × (F i).TopIndex
  let C (j : J) := (F j.1).TopFactor j.2
  have hC (j : J) : Module.Critical Rᵐᵒᵖ (e j.1) (C j) :=
    (F j.1).topFactor_critical j.2
  have htC (j : J) : IsGoldieTorsion R (C j) := by
    let U := (F j.1).toRelSeries j.2.val.succ
    let V := ((F j.1).toRelSeries j.2.val.castSucc).comap U.subtype
    exact IsGoldieTorsion.of_surjective V.mkQ V.mkQ_surjective
      (IsGoldieTorsion.of_injective U.subtype Subtype.val_injective (ht j.1))
  obtain ⟨H, hH⟩ := exists_affine_germ_tests (k := k)
    (fun j : J => e j.1) (fun j => M j.1) C
    (fun j => hM j.1) hC htC (fun j => q j.1) (fun j => z j.1)
    (fun j => hq j.1) (fun j => b j.1) (fun j => hb j.1) ha B
  exact ⟨H, fun i => (Hom.epic_iff_injective_comp_topFactors (hM i) (F i) _).mpr
    (fun j => hH ⟨i, j⟩)⟩

end Selection

/-! ## Tests with Goldie-torsion targets and regular tails -/

/-- A single actual epic germ test (a test of §3): Goldie-torsion target of
finite deviation, epic germ `q`, offset germ, regular tail. -/
structure GoldieGermTest (R : Type u) [Ring R] where
  level : ℕ
  Target : Type u
  [addCommGroup : AddCommGroup Target]
  [module : Module Rᵐᵒᵖ Target]
  [noetherian : IsNoetherian Rᵐᵒᵖ Target]
  bounded : Module.DevLE Rᵐᵒᵖ level Target
  torsion : IsGoldieTorsion R Target
  q : Hom Rᵐᵒᵖ level R Target
  offset : Hom Rᵐᵒᵖ level R Target
  epic : Hom.Epic q
  tail : R
  tail_reg : tail ∈ R⁰

attribute [instance] GoldieGermTest.addCommGroup GoldieGermTest.module
  GoldieGermTest.noetherian

section Tests

variable {R : Type u} [Ring R]

/-- `f` satisfies the test if `offset + q f tail` is epic. -/
def GoldieGermTest.Satisfied (t : GoldieGermTest R) (f : R) : Prop :=
  Hom.Epic (t.offset + op (f * t.tail) • t.q)

/-- Pencil stability (Lemma 3.6): a satisfied test has only finitely many bad
central corrections. -/
theorem GoldieGermTest.pencil_finite {k : Type*} [Field k] [Algebra k R]
    (t : GoldieGermTest R) {f : R} (hf : t.Satisfied f) (g : R) :
    {c : k | ¬ t.Satisfied (f + algebraMap k R c * g)}.Finite := by
  classical
  let F := Classical.choice t.bounded.nonempty_criticalFiltration
  have hfin := germ_pencil_finite (k := k) t.bounded F
    (t.offset + op (f * t.tail) • t.q) (op (g * t.tail) • t.q) hf
  simpa only [GoldieGermTest.Satisfied,
    test_pencil_identity _ _ _ _ _ _ (fun x => (Algebra.commutes _ x))] using hfin

/-- The unit test `(e, R/J, q_J, 0, 1)` of §4 step 3. -/
def unitTest [IsNoetherian Rᵐᵒᵖ R] (J : Submodule Rᵐᵒᵖ R) (e : ℕ)
    (hJ : Module.DevLE Rᵐᵒᵖ e (R ⧸ J)) (hT : IsGoldieTorsion R (R ⧸ J)) :
    GoldieGermTest R where
  level := e
  Target := R ⧸ J
  bounded := hJ
  torsion := hT
  q := Hom.ofLinearMap J.mkQ
  offset := 0
  epic := Hom.epic_ofLinearMap_of_surjective _ (Submodule.mkQ_surjective _)
  tail := 1
  tail_reg := Submonoid.one_mem _

/-- The fixed-ideal induction invariant `P(h)` of §4 with the strict stratum
`Small e`, over arbitrary finite families of Goldie germ tests. -/
def IdealBound (I : Submodule Rᵐᵒᵖ R) (e : ℕ) : Prop :=
  ∀ (x t : R), t ≠ 0 → ∀ {ι : Type u} [Fintype ι] (tests : ι → GoldieGermTest R),
    ∃ H : R, Module.Small Rᵐᵒᵖ e (R ⧸ (I ⊔ principalRightIdeal (x + H * t))) ∧
      ∀ i, (tests i).Satisfied (x + H * t)

end Tests

/-! ## The two-call descent (§4) -/

section Descent

variable {R : Type u} [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
variable {k : Type*} [Field k] [Infinite k] [Algebra k R]

include k in
/-- Base `P(0)`: source selection with the bound inherited from `R/I`. -/
theorem idealBound_initial {I : Submodule Rᵐᵒᵖ R} {N : ℕ}
    (hI : Module.DevLE Rᵐᵒᵖ N (R ⧸ I)) : IdealBound I (N + 1) := by
  intro x t ht ι _ tests
  obtain ⟨H, hH⟩ := exists_affine_epic_tests (k := k)
    (fun i => (tests i).level) (fun i => (tests i).Target)
    (fun i => (tests i).bounded) (fun i => (tests i).torsion)
    (fun i => (tests i).q) (fun i => (tests i).offset) (fun i => (tests i).epic)
    (fun i => (tests i).tail) (fun i => (tests i).tail_reg) ht x
  exact ⟨H, hI.of_surjective (Submodule.factor le_sup_left)
    (Submodule.factor_surjective le_sup_left), hH⟩

include k in
/-- The two-call step `P(h) → P(h+1)` of §4 for a right ideal `I` containing
a regular element. -/
theorem idealBound_step {I : Submodule Rᵐᵒᵖ R} {s : R} (hsI : s ∈ I) (hs : s ∈ R⁰)
    (e : ℕ) (hbound : IdealBound I (e + 1)) : IdealBound I e := by
  classical
  intro x t ht ι _ tests
  -- First call.
  obtain ⟨H, hJ, htests⟩ := hbound x t ht tests
  set f := x + H * t with hf
  set J := I ⊔ principalRightIdeal f with hJdef
  have hTJ : IsGoldieTorsion R (R ⧸ J) :=
    isGoldieTorsion_quotient (Submodule.mem_sup_left hsI) hs
  -- Torsion equation (step 2): a regular `b` with `f b ∈ I`.
  obtain ⟨b, hb, hfb⟩ := exists_mul_mem_of_mem_nonZeroDivisors hsI hs f
  have htb : t * b ≠ 0 := fun h0 => ht (hb.2 t h0)
  -- Second call: offset 0, tail t*b, the single unit test of R/J.
  obtain ⟨H₂, hQ, htest⟩ := hbound 0 (t * b) htb
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
  -- Drop: `q_Q (f + lam g)` is epic, and `Q ≤ J'` by the inclusion (4.2).
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

include k in
/-- Finite descent from `P(0)` to `P(N+1)`. -/
theorem idealBound_descend {I : Submodule Rᵐᵒᵖ R} {s : R} (hsI : s ∈ I) (hs : s ∈ R⁰)
    (e h : ℕ) : IdealBound I (e + h) → IdealBound I e := by
  induction h with
  | zero => exact fun hb => hb
  | succ h ih =>
    intro hb
    exact ih (idealBound_step (k := k) hsI hs (e + h) hb)

include k in
/-- **Theorem A' with tests**, `docs/core-theorem.md` §§1, 4: for a simple
right Noetherian ring with an infinite central field and a right ideal `I`
containing a regular element with `R/I` of finite deviation, every `x`,
`t ≠ 0` and every finite family of Goldie germ tests admit `H` with
`I + (x + H t)R = R` and all tests satisfied. -/
theorem fixed_ideal_with_tests {I : Submodule Rᵐᵒᵖ R} (hreg : ∃ s ∈ I, s ∈ R⁰)
    {N : ℕ} (hdev : Module.DevLE Rᵐᵒᵖ N (R ⧸ I)) (x : R) {t : R} (ht : t ≠ 0)
    {ι : Type u} [Fintype ι] (tests : ι → GoldieGermTest R) :
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
/-- **Theorem A' (fixed ideal)**, `docs/core-theorem.md` §1, zero divisors
allowed: if `I` contains a regular element and `R/I` has finite deviation,
then `I + (x + H t)R = R` for some `H`, for every `x` and every `t ≠ 0`. -/
theorem fixed_ideal {I : Submodule Rᵐᵒᵖ R} (hreg : ∃ s ∈ I, s ∈ R⁰)
    {N : ℕ} (hdev : Module.DevLE Rᵐᵒᵖ N (R ⧸ I)) (x : R) {t : R} (ht : t ≠ 0) :
    ∃ H : R, I ⊔ principalRightIdeal (x + H * t) = ⊤ := by
  obtain ⟨H, hH, _⟩ := fixed_ideal_with_tests (k := k) hreg hdev x ht
    (fun i : PEmpty.{u + 1} => nomatch i)
  exact ⟨H, hH⟩

include k in
/-- **Theorem A (fixed anchor)**, `docs/core-theorem.md` §1, zero divisors
allowed: for a regular anchor `d` with `R/dR` of finite deviation, every
`a ≠ 0` (possibly singular) and every `B`, there are `H, U, V` with
`1 = d U + (B + H a) d V`. Proof: Theorem A' with `I = dR`, `x = Bd`, `t = ad`. -/
theorem fixed_anchor {N : ℕ} {d a : R} (hd : d ∈ R⁰) (ha : a ≠ 0)
    (hdev : Module.DevLE Rᵐᵒᵖ N (R ⧸ anchor d)) (B : R) :
    ∃ H U V : R, 1 = d * U + (B + H * a) * d * V := by
  obtain ⟨H, hH⟩ := fixed_ideal (k := k) (I := anchor d) ⟨d, ⟨1, mul_one d⟩, hd⟩ hdev
    (B * d) (t := a * d) (fun h0 => ha (hd.2 a h0))
  have h1 : (1 : R) ∈ anchor d ⊔ principalRightIdeal (B * d + H * (a * d)) := by
    rw [hH]; exact Submodule.mem_top
  obtain ⟨y, ⟨U, rfl⟩, z, ⟨V, rfl⟩, he⟩ := Submodule.mem_sup.mp h1
  refine ⟨H, U, V, ?_⟩
  rw [← he]
  change d * U + (B * d + H * (a * d)) * V = d * U + (B + H * a) * d * V
  simp only [add_mul, mul_assoc]

end Descent

/-! ## Corollary B (Lemma 6.1) -/

section CorollaryB

variable {R : Type u} [Ring R]

/-- Lemma 6.1: under `Kdim R ≤ ω`, `R/dR` has finite deviation for every
left-regular `d` (in particular every regular `d`). -/
theorem principal_quotient_finite_of_omega (hR : Module.DevLEOmega Rᵐᵒᵖ R)
    {d : R} (hd : d ∈ R⁰) : ∃ n, Module.DevLE Rᵐᵒᵖ n (R ⧸ anchor d) :=
  hR.quotient_range_of_injective (leftMulLinear d) fun x y hxy => by
    have h : d * (x - y) = 0 := by
      rw [mul_sub]
      exact sub_eq_zero.mpr hxy
    exact sub_eq_zero.mp (hd.1 _ h)

/-- **Corollary B (ideals)**, Lemma 6.1: under `Kdim R ≤ ω` every right ideal
containing a regular element has finite-deviation quotient. -/
theorem quotient_finite_of_omega (hR : Module.DevLEOmega Rᵐᵒᵖ R)
    {I : Submodule Rᵐᵒᵖ R} (hreg : ∃ s ∈ I, s ∈ R⁰) :
    ∃ N, Module.DevLE Rᵐᵒᵖ N (R ⧸ I) := by
  obtain ⟨s, hsI, hs⟩ := hreg
  obtain ⟨N, hN⟩ := principal_quotient_finite_of_omega hR hs
  refine ⟨N, quotient_devLE hN I ?_⟩
  rintro y ⟨r, rfl⟩
  exact I.smul_mem (op r) hsI

variable [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
variable {k : Type*} [Field k] [Infinite k] [Algebra k R]

include k in
/-- **Theorem A' under `Kdim R ≤ ω`** (Corollary B). -/
theorem fixed_ideal_of_devLE_omega (hR : Module.DevLEOmega Rᵐᵒᵖ R)
    {I : Submodule Rᵐᵒᵖ R} (hreg : ∃ s ∈ I, s ∈ R⁰) (x : R) {t : R} (ht : t ≠ 0) :
    ∃ H : R, I ⊔ principalRightIdeal (x + H * t) = ⊤ := by
  obtain ⟨N, hN⟩ := quotient_finite_of_omega hR hreg
  exact fixed_ideal (k := k) hreg hN x ht

include k in
/-- **Theorem A under `Kdim R ≤ ω`** (Corollary B). -/
theorem fixed_anchor_of_devLE_omega (hR : Module.DevLEOmega Rᵐᵒᵖ R)
    {d a : R} (hd : d ∈ R⁰) (ha : a ≠ 0) (B : R) :
    ∃ H U V : R, 1 = d * U + (B + H * a) * d * V := by
  obtain ⟨N, hN⟩ := principal_quotient_finite_of_omega hR hd
  exact fixed_anchor (k := k) hd ha hN B

end CorollaryB

/-! ## Corollary C.1 (Lemma 6.2) -/

section CorollaryC1

variable {R : Type u} [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
variable {k : Type*} [Field k] [Infinite k] [Algebra k R]
variable {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]

include k in
/-- The induction of Lemma 6.2 over a finite generating set, relative to an
arbitrary submodule `W`, for Goldie-torsion modules. -/
theorem prescribed_cyclic_aux
    (hcyc : ∀ u : M, ∃ N, Module.DevLE Rᵐᵒᵖ N (R ⧸ LinearMap.ker (cyclicMap (R := R) u)))
    (htor : IsGoldieTorsion R M) {t : R} (ht : t ≠ 0) (s : Finset M) :
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
    have hreg : ∃ s ∈ LinearMap.ker (cyclicMap (R := R) u), s ∈ R⁰ := ⟨s₀, hs₀u, hs₀⟩
    obtain ⟨H, hH⟩ := fixed_ideal (k := k) hreg hN 0 (t := t * b)
      (fun h0 => ht (hb.2 t h0))
    rw [zero_add] at hH
    have h1 : (1 : R) ∈ LinearMap.ker (cyclicMap (R := R) u) ⊔
        principalRightIdeal (H * (t * b)) := by rw [hH]; exact Submodule.mem_top
    obtain ⟨i, hi, w, ⟨r, rfl⟩, hiw⟩ := Submodule.mem_sup.mp h1
    set kk := op H • u with hkk
    set z := c + op t • kk with hz
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
    (htor : IsGoldieTorsion R M) (x : M) {t : R} (ht : t ≠ 0) :
    ∃ h : M, Submodule.span Rᵐᵒᵖ {x + op t • h} = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Rᵐᵒᵖ) (M := M)
  obtain ⟨h, hh⟩ := prescribed_cyclic_aux (k := k) hcyc htor ht s ⊥
    (by rw [hs, top_sup_eq]) x
  exact ⟨h, by rwa [sup_bot_eq] at hh⟩

include k in
/-- **Corollary C.1**, Lemma 6.2, zero divisors allowed: a finitely generated
Goldie-torsion right module of finite deviation is cyclic with prescribed
affine generator `x + h t`, for every `x` and every `t ≠ 0`. -/
theorem prescribed_cyclic [Module.Finite Rᵐᵒᵖ M]
    (htor : IsGoldieTorsion R M) {N : ℕ} (hM : Module.DevLE Rᵐᵒᵖ N M)
    (x : M) {t : R} (ht : t ≠ 0) :
    ∃ h : M, Submodule.span Rᵐᵒᵖ {x + op t • h} = ⊤ :=
  prescribed_cyclic_of_cyclic (k := k) (fun u => ⟨N, devLE_cyclic hM u⟩) htor x ht

include k in
/-- **Corollary C.1 under (H_all)**: if `R/dR` has finite deviation for every
regular `d`, the dimension hypothesis is automatic. -/
theorem prescribed_cyclic_of_principal [Module.Finite Rᵐᵒᵖ M]
    (hall : ∀ d : R, d ∈ R⁰ → ∃ N, Module.DevLE Rᵐᵒᵖ N (R ⧸ anchor d))
    (htor : IsGoldieTorsion R M) (x : M) {t : R} (ht : t ≠ 0) :
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
    (htor : IsGoldieTorsion R M) (x : M) {t : R} (ht : t ≠ 0) :
    ∃ h : M, Submodule.span Rᵐᵒᵖ {x + op t • h} = ⊤ :=
  prescribed_cyclic_of_principal (k := k)
    (fun _ hd => principal_quotient_finite_of_omega hR hd) htor x ht

end CorollaryC1

/-! ## Corollary C.2 (Lemma 6.3) -/

section CorollaryC2

variable {R : Type u} [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
variable {k : Type*} [Field k] [Infinite k] [Algebra k R]

include k in
/-- **Corollary C.2** (Lemma 6.3), zero divisors allowed, under (H_all): if
`a ∈ I` and every `y ∈ I` has a regular `s` with `y s ∈ aR` (the elementwise
content of `aQ = IQ`), then for every `y ∈ I` and `t ≠ 0` some `h ∈ I` gives
`I = aR + (y + h t)R`. -/
theorem two_generated_of_principal
    (hall : ∀ d : R, d ∈ R⁰ → ∃ N, Module.DevLE Rᵐᵒᵖ N (R ⧸ anchor d))
    {I : Submodule Rᵐᵒᵖ R} {a : R} (haI : a ∈ I)
    (hIa : ∀ y ∈ I, ∃ s ∈ R⁰, y * s ∈ principalRightIdeal a)
    {y : R} (hyI : y ∈ I) {t : R} (ht : t ≠ 0) :
    ∃ h ∈ I, I = principalRightIdeal a ⊔ principalRightIdeal (y + h * t) := by
  classical
  set K := (principalRightIdeal a).comap I.subtype
  obtain ⟨hbar, hh⟩ := prescribed_cyclic_of_principal (k := k) (M := ↥I ⧸ K) hall
    (isGoldieTorsion_quotient_of_forall_exists_mul_mem hIa) (K.mkQ ⟨y, hyI⟩) ht
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
    {I : Submodule Rᵐᵒᵖ R} {a : R} (haI : a ∈ I)
    (hIa : ∀ y ∈ I, ∃ s ∈ R⁰, y * s ∈ principalRightIdeal a)
    {y : R} (hyI : y ∈ I) {t : R} (ht : t ≠ 0) :
    ∃ h ∈ I, I = principalRightIdeal a ⊔ principalRightIdeal (y + h * t) :=
  two_generated_of_principal (k := k)
    (fun _ hd => principal_quotient_finite_of_omega hR hd) haI hIa hyI ht

/-- For a regular `a`, the hypothesis of Corollary C.2 holds for every right
ideal `I` (right Ore condition for regular elements, Goldie). -/
theorem exists_mul_mem_principal_of_regular {a : R} (ha : a ∈ R⁰) (I : Submodule Rᵐᵒᵖ R) :
    ∀ y ∈ I, ∃ s ∈ R⁰, y * s ∈ principalRightIdeal a :=
  fun y _ => exists_mul_mem_of_mem_nonZeroDivisors (I := principalRightIdeal a) ⟨1, mul_one a⟩ ha y

include k in
/-- **Corollary C.2 for a regular generator**, under (H_all): if `I` contains a
regular `a`, then for every `y ∈ I` and `t ≠ 0` some `h ∈ I` gives
`I = aR + (y + h t)R`. -/
theorem two_generated_of_regular
    (hall : ∀ d : R, d ∈ R⁰ → ∃ N, Module.DevLE Rᵐᵒᵖ N (R ⧸ anchor d))
    {I : Submodule Rᵐᵒᵖ R} {a : R} (haI : a ∈ I) (ha : a ∈ R⁰)
    {y : R} (hyI : y ∈ I) {t : R} (ht : t ≠ 0) :
    ∃ h ∈ I, I = principalRightIdeal a ⊔ principalRightIdeal (y + h * t) :=
  two_generated_of_principal (k := k) hall haI
    (exists_mul_mem_principal_of_regular ha I) hyI ht

end CorollaryC2

end GeneralizedStafford.FixedAnchor.Regular
