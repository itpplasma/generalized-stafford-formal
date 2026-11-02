module

public import GeneralizedStafford.Germs

@[expose] public section

/-!
# The two-call descent

Paper: `docs/core-theorem.md`, Section 4 (proof of Theorem A'); manuscript
`docs/manuscript/main.tex`, Section 4 (`sec:descent`).

Fix a right ideal `I` containing a regular element `s`. With `N = Kdim(R/I)`,
the assertion `P(h)` of the paper is `IdealBound I e` for `e = N - h + 1`: for
all `x`, all `t ≠ 0` and every finite family of tests there is `f = x + H t`
satisfying the tests with `Kdim R/(I + fR) < e`. (The strict stratum
`Kdim < e` is `Module.Small Rᵐᵒᵖ e`, so `Kdim ≤ N - h` is `Small (N - h + 1)`.)

* **Base `P(0)`** (`idealBound_initial`): source selection, Lemma 3.6.
* **Step `P(h) → P(h+1)`** (`idealBound_step`): the eight steps of Section 4.
  The first call gives `f = x + H t` and `J = I + fR`; a regular `b` with
  `f b ∈ I` exists by Goldie (I1); the second call, for the same `I`, with
  offset `0`, tail `t b` and the single unit test of `R/J`, gives `g b` with
  `Q = I + g b R`; then `q_Q f` is epic, a good nonzero central `λ` keeps
  `q_Q (f + λ g)` epic and all old tests satisfied, the inclusion (4.2) gives
  `Q ⊆ I + (f + λ g)R`, so the dimension drops, and
  `f + λ g = x + (H + λ H₂) t`.
* **Termination (E2)** (`idealBound_zero`): `N + 1` steps reach `P(N+1)`,
  i.e. `Kdim R/(I + fR) < 0`.
-/

namespace GeneralizedStafford

open Module Module.Germ MulOpposite nonZeroDivisors
open AlgebraicAnalysis AlgebraicAnalysis.Goldie AlgebraicAnalysis.DenominatorTorsion

universe u

variable {R : Type u} [Ring R]

/-- The induction assertion `P(h)` of Section 4, with `e = N - h + 1`: for all
`x`, all `t ≠ 0` and every finite family of tests there is `H` such that
`f = x + H t` satisfies the tests and `Kdim R/(I + fR) < e`. -/
def IdealBound (I : Submodule Rᵐᵒᵖ R) (e : ℕ) : Prop :=
  ∀ (x t : R), t ≠ 0 → ∀ {ι : Type u} [Fintype ι] (tests : ι → GermTest R),
    ∃ H : R, Module.Small Rᵐᵒᵖ e (R ⧸ (I ⊔ principalRightIdeal (x + H * t))) ∧
      ∀ i, (tests i).Satisfied (x + H * t)

/-- **The inclusion (4.2).** If `f b ∈ I` and `λ` is a central unit, then
`g b ∈ I + (f + λ g)R`, since `g b λ = (f + λ g) b - f b`. -/
theorem mul_mem_sup_pencil {I : Submodule Rᵐᵒᵖ R} {f g b lam : R}
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

/-- The central correction stays in the affine coset:
`(x + H t) + λ (H₂ t) = x + (H + λ H₂) t` (Section 4, step 8). -/
theorem affine_update (x H H₂ t lam : R) :
    (x + H * t) + lam * (H₂ * t) = x + (H + lam * H₂) * t := by
  simp only [add_mul, mul_assoc, add_assoc]

variable [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
variable {k : Type*} [Field k] [Infinite k] [Algebra k R]

include k in
/-- **Base `P(0)`.** If `Kdim R/I ≤ N`, then `IdealBound I (N + 1)`: source
selection (Lemma 3.6) gives the tests, and `R/(I + fR)` is a quotient of
`R/I`. -/
theorem idealBound_initial {I : Submodule Rᵐᵒᵖ R} {N : ℕ}
    (hfin : Module.DevLE Rᵐᵒᵖ N (R ⧸ I)) : IdealBound I (N + 1) := by
  intro x t ht ι _ tests
  obtain ⟨H, hH⟩ := GermTest.exists_affine_satisfied k tests x ht
  exact ⟨H, hfin.of_surjective (Submodule.factor le_sup_left)
    (Submodule.factor_surjective le_sup_left), hH⟩

include k in
/-- **The two-call step `P(h) → P(h+1)`** for a right ideal `I` containing a
regular element `s`: `IdealBound I (e + 1)` implies `IdealBound I e`. -/
theorem idealBound_step {I : Submodule Rᵐᵒᵖ R} {s : R} (hsI : s ∈ I) (hs : s ∈ R⁰)
    (e : ℕ) (hbound : IdealBound I (e + 1)) : IdealBound I e := by
  classical
  intro x t ht ι _ tests
  -- Step 1 (first call): `f = x + H t` satisfies the tests, `Kdim R/J ≤ e`.
  obtain ⟨H, hJ, htests⟩ := hbound x t ht tests
  set f := x + H * t with hf
  set J := I ⊔ principalRightIdeal f with hJdef
  -- Step 2 (torsion equation): a regular `b` with `f b ∈ I` (Goldie, I1).
  obtain ⟨b, hb, hfb⟩ := exists_mul_mem_of_mem_nonZeroDivisors hsI hs f
  have htb : t * b ≠ 0 := fun h0 => ht (hb.2 t h0)
  -- Step 3 (second call, same `I`): offset `0`, tail `t b`, the unit test of `R/J`.
  obtain ⟨H₂, hQ, htest⟩ := hbound 0 (t * b) htb
    (fun _ : PUnit.{u + 1} => unitTest J e hJ
      (isGoldieTorsion_quotient (Submodule.mem_sup_left hsI) hs))
  set g := H₂ * t with hg
  have hgb : (0 : R) + H₂ * (t * b) = g * b := by rw [zero_add, hg, mul_assoc]
  have htJ := (unitTest_satisfied_iff _ _ _ _ _).mp (htest PUnit.unit)
  rw [hgb] at hQ htJ
  set Q := I ⊔ principalRightIdeal (g * b) with hQdef
  -- Step 4 (vanishing of the joint top): `J + g b R = Q + f R`, so `v = q_Q f` is epic.
  have hjoint : J ⊔ principalRightIdeal (g * b) = Q ⊔ principalRightIdeal f := by
    rw [hJdef, hQdef, sup_assoc, sup_assoc, sup_comm (principalRightIdeal f)]
  rw [hjoint] at htJ
  have hv : Hom.Epic (op f • Hom.ofLinearMap (e := e) Q.mkQ) :=
    (smul_mkQ_epic_iff Q f).mpr htJ
  -- Step 5 (good central scalar): `λ ≠ 0` outside the finitely many exceptions.
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
  -- Step 6 (inclusion (4.2)): `Q ⊆ J' = I + (f + λ g)R`.
  have hideal : Q ⊔ principalRightIdeal (f + lam * g) =
      I ⊔ principalRightIdeal (f + lam * g) := by
    apply le_antisymm
    · refine sup_le (sup_le le_sup_left ?_) le_sup_right
      rintro y ⟨r, rfl⟩
      exact Submodule.smul_mem _ (op r) (mul_mem_sup_pencil hfb hlam hunit)
    · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  -- Step 7 (drop): `q_Q (f + λ g) = v + u λ` is epic, so `Kdim R/J' < e`.
  have hep' : Hom.Epic (op (f + lam * g) • Hom.ofLinearMap (e := e) Q.mkQ) := by
    have hid := test_pencil_identity (Hom.ofLinearMap (e := e) Q.mkQ) 0 f g 1 lam hlam
    simp only [mul_one, zero_add] at hid
    rwa [hid]
  have hsmall := (smul_mkQ_epic_iff Q (f + lam * g)).mp hep'
  rw [hideal] at hsmall
  -- Step 8 (affine form): `f + λ g = x + (H + λ H₂) t`.
  have heq : f + lam * g = x + (H + lam * H₂) * t := affine_update x H H₂ t lam
  rw [heq] at hsmall hkeep
  exact ⟨H + lam * H₂, hsmall, hkeep⟩

include k in
/-- **Termination (E2).** If `I` contains a regular element and
`Kdim R/I ≤ N`, then `IdealBound I 0`: the `N + 1` steps from `P(0)` reach
`P(N+1)`. -/
theorem idealBound_zero {I : Submodule Rᵐᵒᵖ R} (hreg : ∃ s ∈ I, s ∈ R⁰)
    {N : ℕ} (hfin : Module.DevLE Rᵐᵒᵖ N (R ⧸ I)) : IdealBound I 0 := by
  obtain ⟨s, hsI, hs⟩ := hreg
  have descend : ∀ h, IdealBound I h → IdealBound I 0 := fun h => by
    induction h with
    | zero => exact id
    | succ h ih => exact fun hb => ih (idealBound_step (k := k) hsI hs h hb)
  exact descend (N + 1) (idealBound_initial (k := k) hfin)

end GeneralizedStafford
