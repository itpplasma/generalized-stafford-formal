import GeneralizedStafford.Challenge.Transport
import GeneralizedStafford.Challenge.WeylTransport
import GeneralizedStafford.Challenge.FilteredTransport
import GeneralizedStafford.Challenge.EnvelopingTransport
import GeneralizedStafford.Challenge.DiffOpTransport

/-!
# Solution: Theorem A', Theorem A and Corollaries B and C

Palomar solution module for `GeneralizedStaffordChallenge.lean`. The definitions
of the challenge are restated verbatim in
`GeneralizedStafford/Challenge/Transport.lean`, which this file imports; this file
does not import the challenge. Each theorem below has the exact name and type of
the compared challenge declaration and is the proof `<name>_proof` of the
transport file.

All thirty-nine compared challenge theorems are solved: the eleven Theorem A' / Theorem A and
Corollary B and C statements, the two Weyl two-generation statements and the nine Weyl algebra
statements (proved in `GeneralizedStafford/Challenge/Transport.lean` and `WeylTransport.lean`),
the six filtered-ring statements (`FilteredTransport.lean`), the five simple-quotient statements
of enveloping algebras (`EnvelopingTransport.lean`), and the six differential-operator statements
of `D_k(A)`, proved in `GeneralizedStafford/Challenge/DiffOpTransport.lean` from
`GeneralizedStafford/DifferentialOperators.lean` and the AlgebraicAnalysis differential operators.
-/

universe u v

namespace GeneralizedStaffordChallenge

/-- Theorem A' (fixed ideal). -/
theorem fixedIdeal : FixedIdealStatement.{u} :=
  fixedIdeal_proof.{u}

/-- Theorem A (fixed anchor). -/
theorem fixedAnchor : FixedAnchorStatement.{u} :=
  fixedAnchor_proof.{u}

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

/-- Two generators for right ideals of the Weyl algebra `Aₙ(k)`. -/
theorem weylTwoGeneratedRight : WeylTwoGeneratedRightStatement.{u} :=
  weylTwoGeneratedRight_proof.{u}

/-- Two generators for left ideals of the Weyl algebra `Aₙ(k)`. -/
theorem weylTwoGeneratedLeft : WeylTwoGeneratedLeftStatement.{u} :=
  weylTwoGeneratedLeft_proof.{u}

/-- Stafford's Conjecture 3.8 for `Aₙ(k)`: for every nonzero `d` there are `F, R, S` with `1 = d R + F d S`. -/
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

/-- Filtered rings: (N), (Z) and `Kdim ≤ m` on both sides. -/
theorem filteredHypotheses : FilteredHypothesesStatement.{u} :=
  filteredHypotheses_proof.{u}

/-- Filtered rings: Theorem A, right and left forms. -/
theorem filteredTheoremA : FilteredTheoremAStatement.{u} :=
  filteredTheoremA_proof.{u}

/-- Filtered rings: Theorem A' on both sides. -/
theorem filteredFixedIdeal : FilteredFixedIdealStatement.{u} :=
  filteredFixedIdeal_proof.{u}

/-- Filtered rings: Corollary C.1 (prescribed and stable) on both sides. -/
theorem filteredPrescribedCyclic : FilteredPrescribedCyclicStatement.{u, v} :=
  filteredPrescribedCyclic_proof.{u, v}

/-- Filtered rings: Corollary C.2 on both sides. -/
theorem filteredTwoGenerated : FilteredTwoGeneratedStatement.{u} :=
  filteredTwoGenerated_proof.{u}

/-- Filtered rings with a domain as associated graded ring: Theorem A for every
nonzero anchor, on both sides. -/
theorem filteredDomain : FilteredDomainStatement.{u} :=
  filteredDomain_proof.{u}

/-- Simple quotients of enveloping algebras: (N), (Z) and `Kdim ≤ dim 𝔤` on both sides. -/
theorem envelopingHypotheses : EnvelopingHypothesesStatement.{u} :=
  envelopingHypotheses_proof.{u}

/-- Simple quotients of enveloping algebras: Theorem A, both forms (right and left). -/
theorem envelopingTheoremA : EnvelopingTheoremAStatement.{u} :=
  envelopingTheoremA_proof.{u}

/-- Simple quotients of enveloping algebras: Theorem A' on both sides. -/
theorem envelopingFixedIdeal : EnvelopingFixedIdealStatement.{u} :=
  envelopingFixedIdeal_proof.{u}

/-- Simple quotients of enveloping algebras: Corollary C.1 on both sides. -/
theorem envelopingPrescribedCyclic : EnvelopingPrescribedCyclicStatement.{u, v} :=
  envelopingPrescribedCyclic_proof.{u, v}

/-- Simple quotients of enveloping algebras: Corollary C.2 on both sides. -/
theorem envelopingTwoGenerated : EnvelopingTwoGeneratedStatement.{u} :=
  envelopingTwoGenerated_proof.{u}


/-! ## Differential operators on a smooth affine variety -/

/-- Two generators for right ideals of `D_k(A)`. -/
theorem diffOpTwoGeneratedRight : DiffOpTwoGeneratedRightStatement.{u} :=
  diffOpTwoGeneratedRight_proof.{u}

/-- Two generators for left ideals of `D_k(A)`. -/
theorem diffOpTwoGeneratedLeft : DiffOpTwoGeneratedLeftStatement.{u} :=
  diffOpTwoGeneratedLeft_proof.{u}

/-- Theorem A for `D_k(A)`, right and left forms. -/
theorem diffOpFixedAnchor : DiffOpFixedAnchorStatement.{u} :=
  diffOpFixedAnchor_proof.{u}

/-- The Global Stafford identity for `D_k(A)`. -/
theorem diffOpGlobalStafford : DiffOpGlobalStaffordStatement.{u} :=
  diffOpGlobalStafford_proof.{u}

/-- Finitely generated torsion right `D_k(A)`-modules are cyclic. -/
theorem diffOpCyclicRight : DiffOpCyclicRightStatement.{u, v} :=
  diffOpCyclicRight_proof.{u, v}

/-- Finitely generated torsion left `D_k(A)`-modules are cyclic. -/
theorem diffOpCyclicLeft : DiffOpCyclicLeftStatement.{u, v} :=
  diffOpCyclicLeft_proof.{u, v}

end GeneralizedStaffordChallenge
