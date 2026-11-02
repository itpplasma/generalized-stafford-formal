import GeneralizedStafford.Filtered
import AlgebraicAnalysis.Enveloping.Presentation
import AlgebraicAnalysis.Filtration.Opposite

/-!
# Simple quotients of enveloping algebras

Example "enveloping algebras" of the manuscript. Let `𝔤` be a finite-dimensional Lie
algebra over an infinite field `k`, and let `R` be a simple `k`-algebra with a surjective
`k`-algebra map `π : U(𝔤) → R` (so `R ≅ U(𝔤)/J` for a two-sided ideal `J`). Then `R` and
`Rᵐᵒᵖ` satisfy (N), (Z) and `Kdim ≤ dim 𝔤`, and hence Theorem A, Theorem A', Corollary B
and Corollary C hold for `R` on both sides.

Proof idea. The PBW symbol presentation of AlgebraicAnalysis (`pbwSymbolPresentation`)
presents the filtration of `R` induced by the generators of `𝔤` by the polynomial ring in
`dim 𝔤` variables, so `R` is Noetherian on both sides with deviation at most `dim 𝔤`. The
opposite statements are the same statements for left ideals, transported by
`isNoetherian_right_op_iff` and `devLE_right_op_iff`. The conclusions then follow from the
abstract theorems of `GeneralizedStafford.Filtered`, using `Module.DevLE.omega`.

* `GeneralizedStafford.enveloping_hypotheses`: (N), (Z) and `Kdim ≤ dim 𝔤` on both sides.
* `GeneralizedStafford.enveloping_theoremA` and the following theorems: the conclusions
  for each side.
-/

universe u v

namespace GeneralizedStafford

open MulOpposite nonZeroDivisors AlgebraicAnalysis AlgebraicAnalysis.Goldie
open AlgebraicAnalysis.DenominatorTorsion AlgebraicAnalysis.Enveloping

section Hypotheses

variable {k : Type*} [Field k] {L : Type*} [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
variable {R : Type u} [Ring R] [Algebra k R]

/-- **Enveloping algebras: (N), (Z) and `Kdim ≤ dim 𝔤` on both sides.** Let `k` be an
infinite field, `𝔤` a finite-dimensional Lie algebra and `R` a simple quotient of `U(𝔤)`,
given by a surjective algebra map `π`. Then `R` is Noetherian with infinite centre and
right deviation at most `dim 𝔤` and at most `ω`; the same holds for `Rᵐᵒᵖ`. -/
theorem enveloping_hypotheses [Infinite k] [IsSimpleRing R]
    (π : UniversalEnvelopingAlgebra k L →ₐ[k] R) (hπ : Function.Surjective π) :
    (IsNoetherian Rᵐᵒᵖ R ∧ Infinite (Subring.center R) ∧
        Module.DevLE Rᵐᵒᵖ (Module.finrank k L) R ∧
        Module.DevLEOmega Rᵐᵒᵖ R) ∧
      (IsNoetherian Rᵐᵒᵖᵐᵒᵖ Rᵐᵒᵖ ∧ Infinite (Subring.center Rᵐᵒᵖ) ∧
        Module.DevLE Rᵐᵒᵖᵐᵒᵖ (Module.finrank k L) Rᵐᵒᵖ ∧
        Module.DevLEOmega Rᵐᵒᵖᵐᵒᵖ Rᵐᵒᵖ) := by
  have hD := devLE_right_of_surjective π hπ
  have hDL : Module.DevLE R (Module.finrank k L) R := devLE_left_of_surjective π hπ
  have hop : IsNoetherian Rᵐᵒᵖᵐᵒᵖ Rᵐᵒᵖ := (isNoetherian_right_op_iff R).mpr (isNoetherianRing_of_surjective π hπ)
  have hopD : Module.DevLE Rᵐᵒᵖᵐᵒᵖ (Module.finrank k L) Rᵐᵒᵖ := (devLE_right_op_iff R _).mpr hDL
  exact ⟨⟨isNoetherian_right_of_surjective π hπ, infinite_subring_center k R, hD, hD.omega⟩,
    ⟨hop, infinite_subring_center k Rᵐᵒᵖ, hopD, hopD.omega⟩⟩

end Hypotheses

section Conclusions

variable {k : Type*} [Field k] [Infinite k] {L : Type*} [LieRing L] [LieAlgebra k L]
  [FiniteDimensional k L] {R : Type u} [Ring R] [IsSimpleRing R] [Algebra k R]

/-- **Theorem A, both sides (enveloping algebras).** For every regular `d`, every nonzero
`a` and every `B` there are `H, U, V` with `1 = d U + (B + H a) d V`, in `R` and in `Rᵐᵒᵖ`
(the left form `1 = U d + V d (B + a H)` of `R`). -/
theorem enveloping_theoremA (π : UniversalEnvelopingAlgebra k L →ₐ[k] R)
    (hπ : Function.Surjective π) :
    (∀ d a B : R, d ∈ R⁰ → a ≠ 0 → ∃ H U V : R, 1 = d * U + (B + H * a) * d * V) ∧
      (∀ d a B : Rᵐᵒᵖ, d ∈ Rᵐᵒᵖ⁰ → a ≠ 0 →
        ∃ H U V : Rᵐᵒᵖ, 1 = d * U + (B + H * a) * d * V) := by
  obtain ⟨⟨hN, -, -, hO⟩, ⟨hN', -, -, hO'⟩⟩ := enveloping_hypotheses π hπ
  have := hN
  have := hN'
  exact ⟨fun d a B hd ha => fixed_anchor_of_devLE_omega (k := k) hO hd ha B,
    fun d a B hd ha => fixed_anchor_of_devLE_omega (k := k) hO' hd ha B⟩

/-- **Theorem A', both sides (enveloping algebras).** For every right ideal `I` of `R`
containing a regular element, every `x` and every nonzero `t` there is `H` with
`I + (x + H t) R = R`; the same holds for `Rᵐᵒᵖ`. -/
theorem enveloping_fixedIdeal (π : UniversalEnvelopingAlgebra k L →ₐ[k] R)
    (hπ : Function.Surjective π) :
    (∀ I : Submodule Rᵐᵒᵖ R, (∃ s ∈ I, s ∈ R⁰) → ∀ x t : R, t ≠ 0 →
        ∃ H : R, I ⊔ principalRightIdeal (x + H * t) = ⊤) ∧
      (∀ I : Submodule Rᵐᵒᵖᵐᵒᵖ Rᵐᵒᵖ, (∃ s ∈ I, s ∈ Rᵐᵒᵖ⁰) → ∀ x t : Rᵐᵒᵖ, t ≠ 0 →
        ∃ H : Rᵐᵒᵖ, I ⊔ principalRightIdeal (x + H * t) = ⊤) := by
  obtain ⟨⟨hN, -, -, hO⟩, ⟨hN', -, -, hO'⟩⟩ := enveloping_hypotheses π hπ
  have := hN
  have := hN'
  exact ⟨fun I hreg x t ht => by
      obtain ⟨H, hH⟩ := fixed_ideal_of_devLE_omega (k := k) hO hreg x ht
      exact ⟨H, hH⟩,
    fun I hreg x t ht => by
      obtain ⟨H, hH⟩ := fixed_ideal_of_devLE_omega (k := k) hO' hreg x ht
      exact ⟨H, hH⟩⟩

/-- **Corollary B, both sides (enveloping algebras).** `R` has `Kdim (R / dR)` finite for
every regular `d`, and `Kdim (R / I)` finite for every right ideal `I` containing a regular
element; the same holds for `Rᵐᵒᵖ`. -/
theorem enveloping_corollaryB (π : UniversalEnvelopingAlgebra k L →ₐ[k] R)
    (hπ : Function.Surjective π) :
    (PrincipalQuotientsFinite R ∧
        ∀ I : Submodule Rᵐᵒᵖ R, (∃ s ∈ I, s ∈ R⁰) → ∃ N, Module.DevLE Rᵐᵒᵖ N (R ⧸ I)) ∧
      (PrincipalQuotientsFinite Rᵐᵒᵖ ∧
        ∀ I : Submodule Rᵐᵒᵖᵐᵒᵖ Rᵐᵒᵖ, (∃ s ∈ I, s ∈ Rᵐᵒᵖ⁰) →
          ∃ N, Module.DevLE Rᵐᵒᵖᵐᵒᵖ N (Rᵐᵒᵖ ⧸ I)) := by
  obtain ⟨⟨hN, -, -, hO⟩, ⟨hN', -, -, hO'⟩⟩ := enveloping_hypotheses π hπ
  have := hN
  have := hN'
  exact ⟨⟨principalQuotientsFinite_of_devLE_omega hO, fun _ hreg => quotient_finite_of_omega hO hreg⟩,
    ⟨principalQuotientsFinite_of_devLE_omega hO', fun _ hreg => quotient_finite_of_omega hO' hreg⟩⟩

/-- **Corollary C.1, both sides (enveloping algebras).** Every finitely generated
Goldie-torsion right module `M` over `R` (and over `Rᵐᵒᵖ`) satisfies: for every `x ∈ M` and
every nonzero `t` there is `h ∈ M` with `M = (x + h t) R`. Also, for Goldie-torsion elements
`c, u` of `M` and every nonzero `t` there is `H` with `cR + uR = (c + u H t) R`. -/
theorem enveloping_prescribedCyclic (π : UniversalEnvelopingAlgebra k L →ₐ[k] R)
    (hπ : Function.Surjective π) :
    ((∀ (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M],
        IsGoldieTorsion R M → ∀ (x : M) (t : R), t ≠ 0 →
          ∃ h : M, Submodule.span Rᵐᵒᵖ {x + op t • h} = ⊤) ∧
      (∀ (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] (c u : M),
        (∃ s ∈ R⁰, op s • c = 0) → (∃ s ∈ R⁰, op s • u = 0) → ∀ t : R, t ≠ 0 →
          ∃ H : R, Submodule.span Rᵐᵒᵖ {c, u} = Submodule.span Rᵐᵒᵖ {c + op (H * t) • u})) ∧
    ((∀ (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖᵐᵒᵖ M],
        IsGoldieTorsion Rᵐᵒᵖ M → ∀ (x : M) (t : Rᵐᵒᵖ), t ≠ 0 →
          ∃ h : M, Submodule.span Rᵐᵒᵖᵐᵒᵖ {x + op t • h} = ⊤) ∧
      (∀ (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖᵐᵒᵖ M] (c u : M),
        (∃ s ∈ Rᵐᵒᵖ⁰, op s • c = 0) → (∃ s ∈ Rᵐᵒᵖ⁰, op s • u = 0) → ∀ t : Rᵐᵒᵖ, t ≠ 0 →
          ∃ H : Rᵐᵒᵖ, Submodule.span Rᵐᵒᵖᵐᵒᵖ {c, u} =
            Submodule.span Rᵐᵒᵖᵐᵒᵖ {c + op (H * t) • u})) := by
  obtain ⟨⟨hN, -, -, hO⟩, ⟨hN', -, -, hO'⟩⟩ := enveloping_hypotheses π hπ
  have := hN
  have := hN'
  refine ⟨⟨fun M _ _ _ htor x t ht => prescribed_cyclic_of_devLE_omega (k := k) hO htor x ht,
    fun M _ _ c u hc hu t ht => ?_⟩,
    ⟨fun M _ _ _ htor x t ht => prescribed_cyclic_of_devLE_omega (k := k) hO' htor x ht,
    fun M _ _ c u hc hu t ht => ?_⟩⟩
  · obtain ⟨N, hN⟩ := devLE_span_of_torsion (principalQuotientsFinite_of_devLE_omega hO) hu
    exact span_pair_eq_span_affine (k := k) c u hc hu ⟨N, hN⟩ ht
  · obtain ⟨N, hN⟩ := devLE_span_of_torsion (principalQuotientsFinite_of_devLE_omega hO') hu
    exact span_pair_eq_span_affine (k := k) c u hc hu ⟨N, hN⟩ ht

/-- **Corollary C.2, both sides (enveloping algebras).** Let `I` be a right ideal of `R`
and `a ∈ I` with `aQ = IQ`, that is every `y ∈ I` has a regular `s` with `y s ∈ aR`. Then
for every `y ∈ I` and nonzero `t` there is `h ∈ I` with `I = aR + (y + h t) R`, and every
right ideal of `R` is generated by two elements; the same holds for `Rᵐᵒᵖ`. -/
theorem enveloping_twoGenerated (π : UniversalEnvelopingAlgebra k L →ₐ[k] R)
    (hπ : Function.Surjective π) :
    ((∀ (I : Submodule Rᵐᵒᵖ R) (a : R), a ∈ I →
        (∀ y ∈ I, ∃ s ∈ R⁰, y * s ∈ principalRightIdeal a) →
        ∀ y ∈ I, ∀ t : R, t ≠ 0 →
          ∃ h ∈ I, I = principalRightIdeal a ⊔ principalRightIdeal (y + h * t)) ∧
      ∀ I : Submodule Rᵐᵒᵖ R, ∃ a b : R, I = principalRightIdeal a ⊔ principalRightIdeal b) ∧
    ((∀ (I : Submodule Rᵐᵒᵖᵐᵒᵖ Rᵐᵒᵖ) (a : Rᵐᵒᵖ), a ∈ I →
        (∀ y ∈ I, ∃ s ∈ Rᵐᵒᵖ⁰, y * s ∈ principalRightIdeal a) →
        ∀ y ∈ I, ∀ t : Rᵐᵒᵖ, t ≠ 0 →
          ∃ h ∈ I, I = principalRightIdeal a ⊔ principalRightIdeal (y + h * t)) ∧
      ∀ I : Submodule Rᵐᵒᵖᵐᵒᵖ Rᵐᵒᵖ, ∃ a b : Rᵐᵒᵖ,
        I = principalRightIdeal a ⊔ principalRightIdeal b) := by
  obtain ⟨⟨hN, -, -, hO⟩, ⟨hN', -, -, hO'⟩⟩ := enveloping_hypotheses π hπ
  have := hN
  have := hN'
  exact ⟨⟨fun I a haI hIa y hyI t ht => by
        obtain ⟨h, hhI, hI⟩ := two_generated_prescribed (k := k)
          (principalQuotientsFinite_of_devLE_omega hO) haI hIa hyI ht
        exact ⟨h, hhI, hI⟩,
      fun I => two_generated (k := k) (principalQuotientsFinite_of_devLE_omega hO) I⟩,
    ⟨fun I a haI hIa y hyI t ht => by
        obtain ⟨h, hhI, hI⟩ := two_generated_prescribed (k := k)
          (principalQuotientsFinite_of_devLE_omega hO') haI hIa hyI ht
        exact ⟨h, hhI, hI⟩,
      fun I => two_generated (k := k) (principalQuotientsFinite_of_devLE_omega hO') I⟩⟩

/-- **Corollary C.3, both sides (enveloping algebras).** For finitely generated right
modules `M` over `R` (and over `Rᵐᵒᵖ`), with `ℓ` and `s` the uniform dimensions of `M / t(M)`
and of `R_R`: if `M` is generated by `n` elements then `ℓ ≤ n s`, and if `ℓ < q s` then `M`
is generated by `q` elements. -/
theorem enveloping_generatorBounds (π : UniversalEnvelopingAlgebra k L →ₐ[k] R)
    (hπ : Function.Surjective π) :
    ((∀ (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M]
        (n ℓ s : ℕ), (∃ g : Finset M, g.card ≤ n ∧ Submodule.span Rᵐᵒᵖ (g : Set M) = ⊤) →
        Module.UniformDimGE Rᵐᵒᵖ (M ⧸ goldieTorsionPart R M) ℓ →
        Module.UniformDimLE Rᵐᵒᵖ R s → ℓ ≤ n * s) ∧
      (∀ (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M]
        (q ℓ s : ℕ), Module.UniformDimLE Rᵐᵒᵖ (M ⧸ goldieTorsionPart R M) ℓ →
        Module.UniformDimGE Rᵐᵒᵖ R s → ℓ < q * s →
          ∃ g : Finset M, g.card ≤ q ∧ Submodule.span Rᵐᵒᵖ (g : Set M) = ⊤)) ∧
    ((∀ (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖᵐᵒᵖ M]
        (n ℓ s : ℕ), (∃ g : Finset M, g.card ≤ n ∧ Submodule.span Rᵐᵒᵖᵐᵒᵖ (g : Set M) = ⊤) →
        Module.UniformDimGE Rᵐᵒᵖᵐᵒᵖ (M ⧸ goldieTorsionPart Rᵐᵒᵖ M) ℓ →
        Module.UniformDimLE Rᵐᵒᵖᵐᵒᵖ Rᵐᵒᵖ s → ℓ ≤ n * s) ∧
      (∀ (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖᵐᵒᵖ M]
        (q ℓ s : ℕ), Module.UniformDimLE Rᵐᵒᵖᵐᵒᵖ (M ⧸ goldieTorsionPart Rᵐᵒᵖ M) ℓ →
        Module.UniformDimGE Rᵐᵒᵖᵐᵒᵖ Rᵐᵒᵖ s → ℓ < q * s →
          ∃ g : Finset M, g.card ≤ q ∧ Submodule.span Rᵐᵒᵖᵐᵒᵖ (g : Set M) = ⊤)) := by
  obtain ⟨⟨hN, -, -, hO⟩, ⟨hN', -, -, hO'⟩⟩ := enveloping_hypotheses π hπ
  have := hN
  have := hN'
  exact ⟨⟨fun M _ _ _ n ℓ s ⟨g, hg, hspan⟩ hℓ hs => le_mul_of_span_eq_top g hg hspan hℓ hs,
      fun M _ _ _ q ℓ s hℓ hs hq =>
        exists_span_eq_top_of_lt_mul (k := k) (principalQuotientsFinite_of_devLE_omega hO) hℓ hs hq⟩,
    ⟨fun M _ _ _ n ℓ s ⟨g, hg, hspan⟩ hℓ hs => le_mul_of_span_eq_top g hg hspan hℓ hs,
      fun M _ _ _ q ℓ s hℓ hs hq =>
        exists_span_eq_top_of_lt_mul (k := k) (principalQuotientsFinite_of_devLE_omega hO') hℓ hs hq⟩⟩

end Conclusions

end GeneralizedStafford
