import GeneralizedStafford.Challenge.Transport
import GeneralizedStafford.Challenge.WeylTransport

/-!
# Solution: Theorem A', Theorem A and Corollaries B and C

Palomar solution module for `GeneralizedStaffordChallenge.lean`. The definitions
of the challenge are restated verbatim in
`GeneralizedStafford/Challenge/Transport.lean`, which this file imports; this file
does not import the challenge. Each theorem below has the exact name and type of
the compared challenge declaration and is the proof `<name>_proof` of the
transport file.

All twenty-five compared challenge theorems are solved: the fourteen Theorem A' / Theorem A
and Corollary B and C statements, the two Weyl algebra two-generation statements, and the
nine Weyl algebra statements (Conjecture 3.8, the affine form, Theorem A', torsion cyclicity
and prescribed generators, right and left, and prescribed two-generation, right and left),
proved in `GeneralizedStafford/Challenge/WeylTransport.lean`.
-/

universe u v

namespace GeneralizedStaffordChallenge

/-- Theorem A' (fixed ideal). -/
theorem fixedIdeal : FixedIdealStatement.{u} :=
  fixedIdeal_proof.{u}

/-- Theorem A (fixed anchor). -/
theorem fixedAnchor : FixedAnchorStatement.{u} :=
  fixedAnchor_proof.{u}

/-- Corollary B, dimension part. -/
theorem corollaryB_dimension : CorollaryBDimensionStatement.{u} :=
  corollaryB_dimension_proof.{u}

/-- Corollary B for Theorem A. -/
theorem corollaryB_fixedAnchor : CorollaryBFixedAnchorStatement.{u} :=
  corollaryB_fixedAnchor_proof.{u}

/-- Corollary B for Theorem A'. -/
theorem corollaryB_fixedIdeal : CorollaryBFixedIdealStatement.{u} :=
  corollaryB_fixedIdeal_proof.{u}

/-- Corollary C.1 (finite dimension hypothesis). -/
theorem corollaryC1 : CorollaryC1Statement.{u, v} :=
  corollaryC1_proof.{u, v}

/-- Corollary C.1 under (H_all). -/
theorem corollaryC1_hAll : CorollaryC1HAllStatement.{u, v} :=
  corollaryC1_hAll_proof.{u, v}

/-- Corollary C.1 under (H_omega). -/
theorem corollaryC1_omega : CorollaryC1OmegaStatement.{u, v} :=
  corollaryC1_omega_proof.{u, v}

/-- Corollary C.1, stable cyclicity. -/
theorem corollaryC1_stable : CorollaryC1StableStatement.{u, v} :=
  corollaryC1_stable_proof.{u, v}

/-- Corollary C.2, existence of a full-rank element. -/
theorem corollaryC2_fullRank : CorollaryC2FullRankStatement.{u} :=
  corollaryC2_fullRank_proof.{u}

/-- Corollary C.2, prescribed form. -/
theorem corollaryC2_prescribed : CorollaryC2PrescribedStatement.{u} :=
  corollaryC2_prescribed_proof.{u}

/-- Corollary C.2, every right ideal is two-generated. -/
theorem corollaryC2 : CorollaryC2Statement.{u} :=
  corollaryC2_proof.{u}

/-- Corollary C.3, lower bound `⌈ρ(M)⌉ ≤ μ(M)`. -/
theorem corollaryC3_lower : CorollaryC3LowerStatement.{u, v} :=
  corollaryC3_lower_proof.{u, v}

/-- Corollary C.3, upper bound `μ(M) ≤ ⌊ρ(M)⌋ + 1`. -/
theorem corollaryC3_upper : CorollaryC3UpperStatement.{u, v} :=
  corollaryC3_upper_proof.{u, v}

/-- Two generators for right ideals of the Weyl algebra `Aₙ(k)`. -/
theorem weylTwoGeneratedRight : WeylTwoGeneratedRightStatement.{u} :=
  weylTwoGeneratedRight_proof.{u}

/-- Two generators for left ideals of the Weyl algebra `Aₙ(k)`. -/
theorem weylTwoGeneratedLeft : WeylTwoGeneratedLeftStatement.{u} :=
  weylTwoGeneratedLeft_proof.{u}

/-- Stafford's Conjecture 3.8 for `Aₙ(k)`: every nonzero `d` is Stafford-38 (`1 = d R + F d S`). -/
theorem weylConjecture38 : GeneralizedStaffordWeylChallenge.Conjecture38Statement.{u} :=
  weylConjecture38_proof.{u}

/-- Theorem A for `Aₙ(k)`, affine form: `1 = d U + (B + H a) d V` for nonzero `d` and `a`. -/
theorem weylAffineForm : GeneralizedStaffordWeylChallenge.AffineFormStatement.{u} :=
  weylAffineForm_proof.{u}

/-- Theorem A' for `Aₙ(k)`: a nonzero right ideal `I` satisfies `I + (x + H t) Aₙ(k) = Aₙ(k)`. -/
theorem weylFixedIdeal : GeneralizedStaffordWeylChallenge.FixedIdealStatement.{u} :=
  weylFixedIdeal_proof.{u}

/-- Corollary C.1: a finitely generated torsion right `Aₙ(k)`-module is cyclic. -/
theorem weylTorsionCyclicRight : GeneralizedStaffordWeylChallenge.TorsionCyclicRightStatement.{u, v} :=
  weylTorsionCyclicRight_proof.{u, v}

/-- Corollary C.1: a finitely generated torsion left `Aₙ(k)`-module is cyclic. -/
theorem weylTorsionCyclicLeft : GeneralizedStaffordWeylChallenge.TorsionCyclicLeftStatement.{u, v} :=
  weylTorsionCyclicLeft_proof.{u, v}

/-- Corollary C.1, prescribed generator, right modules: `M = (x + h t) Aₙ(k)`. -/
theorem weylPrescribedCyclicRight : GeneralizedStaffordWeylChallenge.PrescribedCyclicRightStatement.{u, v} :=
  weylPrescribedCyclicRight_proof.{u, v}

/-- Corollary C.1, prescribed generator, left modules: `M = Aₙ(k) (x + t h)`. -/
theorem weylPrescribedCyclicLeft : GeneralizedStaffordWeylChallenge.PrescribedCyclicLeftStatement.{u, v} :=
  weylPrescribedCyclicLeft_proof.{u, v}

/-- Corollary C.2, prescribed first generator, right ideals: `I = a Aₙ(k) + (y + h t) Aₙ(k)`. -/
theorem weylPrescribedTwoGeneratedRight : GeneralizedStaffordWeylChallenge.PrescribedTwoGeneratedRightStatement.{u} :=
  weylPrescribedTwoGeneratedRight_proof.{u}

/-- Corollary C.2, prescribed first generator, left ideals: `I = Aₙ(k) a + Aₙ(k) (y + t h)`. -/
theorem weylPrescribedTwoGeneratedLeft : GeneralizedStaffordWeylChallenge.PrescribedTwoGeneratedLeftStatement.{u} :=
  weylPrescribedTwoGeneratedLeft_proof.{u}

end GeneralizedStaffordChallenge
