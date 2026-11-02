import GeneralizedStafford.Challenge.Transport

/-!
# Solution: Theorem A', Theorem A and Corollaries B and C

Palomar solution module for `GeneralizedStaffordChallenge.lean`. The definitions
of the challenge are restated verbatim in
`GeneralizedStafford/Challenge/Transport.lean`, which this file imports; this file
does not import the challenge. Each theorem below has the exact name and type of
the compared challenge declaration and is the proof `<name>_proof` of the
transport file.

All fourteen compared challenge theorems are solved.
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

end GeneralizedStaffordChallenge
