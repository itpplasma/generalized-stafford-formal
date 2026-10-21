module

public import GeneralizedStafford.ConsequencesRank

@[expose] public section

/-!
# Prescribed-tail generation over scalar S1 domains

Right modules use scalars in `Aᵐᵒᵖ`. In particular `op t • x` means `x t`.
Scalar S1, torsion compression, and finite torsion cyclicity already have
their authoritative proofs in `ConsequencesGeneration`; they are reused here.
The rank is `oreRank`, defined using Mathlib's `OreLocalization` in
`ConsequencesRank`. This file supplies the prescribed-offset extension in
§1 of the research dossier's `docs/projective-anchored-width.md`.
-/

namespace GeneralizedStafford.ProjectiveWidth

open MulOpposite Submodule
open scoped nonZeroDivisors

/-- Scalar S1 is the existing same-divisor property; no new assumption is added.
Its witness order in `S38` is `h, u, v`, with `1 = q*u + h*q*v`. -/
abbrev S1 (A : Type*) [Ring A] : Prop := S38 A

variable {A : Type*} [Ring A] [IsDomain A]
variable {M : Type*} [AddCommGroup M] [Module Aᵐᵒᵖ M]

/-- A prescribed offset in a finite torsion module can be completed using
any nonzero right tail. This uses the existing compression theorem. -/
theorem torsion_prescribed_generator (hO : RightOre A) (hS : S1 A)
    [Module.Finite Aᵐᵒᵖ M] (hM : ∀ x : M, IsRightTorsion A x)
    (b : M) {t : A} (ht : t ≠ 0) :
    ∃ y : M, span Aᵐᵒᵖ {b + op t • y} = ⊤ := by
  obtain ⟨w, hw⟩ := isCyclic_of_forall_isRightTorsion hO hS hM
  obtain ⟨h, hh⟩ := two_torsion_eq_span_singleton hO hS (hM b) (hM w) ht
  refine ⟨op h • w, ?_⟩
  rw [smul_smul, ← op_mul, ← hh, span_insert, hw, sup_top_eq]

variable [OreLocalization.OreSet (Aᵐᵒᵖ)⁰]

/-- A nonzero right tail preserves escape from any localized subspace. -/
theorem tail_escape (W : Submodule (QΛ A) (Loc A M)) {w : M}
    (hw : toLoc A M w ∉ W) {t : A} (ht : t ≠ 0) :
    toLoc A M (op t • w) ∉ W := by
  rw [← smul_toLoc]
  have hn : (numLinear A (op t) : QΛ A) ≠ 0 := by
    intro h
    have he := numLinear_injective (Λ := A) (h.trans (map_zero (numLinear A)).symm)
    exact ht (by simpa using he)
  simpa only [numLinear_apply] using (W.smul_mem_iff hn).not.mpr hw

/-- Choose independent localized columns with prescribed offsets and tail.
No torsion splitting is used. -/
theorem independent_prescribed_columns [Module.Finite Aᵐᵒᵖ M] {k : ℕ}
    (hk : k ≤ oreRank A M) (b : Fin k → M) {t : A} (ht : t ≠ 0) :
    ∃ y : Fin k → M,
      LinearIndependent (QΛ A) (fun i => toLoc A M (b i + op t • y i)) := by
  classical
  have := finite_loc (Λ := A) (M := M)
  induction k with
  | zero => exact ⟨fun i => Fin.elim0 i, linearIndependent_empty_type⟩
  | succ k ih =>
    obtain ⟨y, hy⟩ := ih (by omega) (Fin.tail b)
    let v : Fin k → Loc A M := fun i => toLoc A M (Fin.tail b i + op t • y i)
    let W := span (QΛ A) (Set.range v)
    have hW : W ≠ ⊤ := by
      intro h
      have he : Module.finrank (QΛ A) W = k := by
        simpa [W] using finrank_span_eq_card hy
      rw [h, finrank_top] at he
      change oreRank A M = k at he
      omega
    obtain ⟨w, hw⟩ : ∃ w : M, toLoc A M w ∉ W := by
      by_contra h
      apply hW
      apply eq_top_iff.mpr
      rw [← span_range_toLoc (Λ := A) (M := M), span_le]
      rintro _ ⟨w, rfl⟩
      exact not_exists_not.mp h w
    obtain ⟨z, hz⟩ : ∃ z : M, toLoc A M (b 0 + op t • z) ∉ W := by
      by_cases hb : toLoc A M (b 0) ∈ W
      · refine ⟨w, fun h => tail_escape W hw ht ?_⟩
        exact (W.add_mem_iff_right hb).mp (by simpa using h)
      · exact ⟨0, by simpa using hb⟩
    refine ⟨Fin.cons z y, ?_⟩
    have heq : (fun i : Fin (k + 1) => toLoc A M
        (b i + op t • (Fin.cons z y : Fin (k + 1) → M) i)) =
        Fin.cons (toLoc A M (b 0 + op t • z)) v := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [heq]
    exact hy.finCons hz

/-- Exactly `rank(M)+1` prescribed slots suffice, with a common nonzero
right tail. Rank means dimension after Mathlib Ore localization. -/
theorem prescribed_generators_succ (hS : S1 A) [Module.Finite Aᵐᵒᵖ M]
    (b : Fin (oreRank A M + 1) → M) {t : A} (ht : t ≠ 0) :
    ∃ y : Fin (oreRank A M + 1) → M,
      span Aᵐᵒᵖ (Set.range (fun i => b i + op t • y i)) = ⊤ := by
  classical
  have := finite_loc (Λ := A) (M := M)
  obtain ⟨y, hy⟩ := independent_prescribed_columns (le_refl (oreRank A M))
    (Fin.tail b) ht
  let x : Fin (oreRank A M) → M := fun i => Fin.tail b i + op t • y i
  have hspan : span (QΛ A) (Set.range (toLoc A M ∘ x)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    change Module.finrank (QΛ A) (span (QΛ A)
      (Set.range (fun i => toLoc A M (Fin.tail b i + op t • y i)))) = oreRank A M
    rw [finrank_span_eq_card hy, Fintype.card_fin]
  let W := span Aᵐᵒᵖ (Set.range x)
  obtain ⟨z, hz⟩ := torsion_prescribed_generator (rightOre_of_oreSet (Λ := A)) hS
    (isRightTorsion_quotient_of_span x hspan) (W.mkQ (b 0)) ht
  obtain ⟨w, hw⟩ := W.mkQ_surjective z
  refine ⟨Fin.cons w y, ?_⟩
  have htop : W ⊔ span Aᵐᵒᵖ {b 0 + op t • w} = ⊤ := by
    rw [← comap_map_mkQ, map_span, Set.image_singleton, map_add, map_smul, hw, hz,
      comap_top]
  have heq : (fun i : Fin (oreRank A M + 1) =>
      b i + op t • (Fin.cons w y : Fin (oreRank A M + 1) → M) i) =
      Fin.cons (b 0 + op t • w) x := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [heq, Fin.range_cons, span_insert, sup_comm]
  exact htop

/-- Extra prescribed slots may be retained with zero adjustment. -/
theorem prescribed_generators_le (hS : S1 A) [Module.Finite Aᵐᵒᵖ M]
    {L : ℕ} (hL : oreRank A M + 1 ≤ L) (b : Fin L → M) {t : A} (ht : t ≠ 0) :
    ∃ y : Fin L → M,
      span Aᵐᵒᵖ (Set.range (fun i => b i + op t • y i)) = ⊤ := by
  classical
  obtain ⟨y, hy⟩ := prescribed_generators_succ hS (fun i => b (i.castLE hL)) ht
  let z : Fin L → M := fun i => if hi : i.val < oreRank A M + 1 then y ⟨i.val, hi⟩ else 0
  refine ⟨z, eq_top_iff.mpr ?_⟩
  rw [← hy]
  apply span_mono
  rintro _ ⟨i, rfl⟩
  refine ⟨i.castLE hL, ?_⟩
  simp only [z, Fin.val_castLE, dite_eq_left i.isLt]

/-- The prescribed-tail theorem indexed by any finite set of slots. -/
theorem prescribed_generators (hS : S1 A) [Module.Finite Aᵐᵒᵖ M]
    {ι : Type*} [Fintype ι] (hι : oreRank A M + 1 ≤ Fintype.card ι)
    (b : ι → M) {t : A} (ht : t ≠ 0) :
    ∃ y : ι → M,
      span Aᵐᵒᵖ (Set.range (fun i => b i + op t • y i)) = ⊤ := by
  classical
  let e := Fintype.equivFin ι
  obtain ⟨y, hy⟩ := prescribed_generators_le hS hι (b ∘ e.symm) ht
  refine ⟨y ∘ e, ?_⟩
  convert hy using 2
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e i, by simp⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e.symm i, by simp⟩

end GeneralizedStafford.ProjectiveWidth
