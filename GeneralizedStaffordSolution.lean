import GeneralizedStafford.Challenge.Transport

/-!
# Solution: Theorem A', Theorem A and Corollaries B, C.1, C.2 (prescribed form)

Palomar solution module for `GeneralizedStaffordChallenge.lean`. The definitions
of the challenge are restated verbatim in
`GeneralizedStafford/Challenge/Transport.lean`, which this file imports; this file
does not import the challenge. Each theorem below has the exact name and type of
the compared challenge declaration and is the proof `<name>_proof` of the
transport file.

Five challenge statements are not solved yet and are deliberately absent here:
`corollaryC1_stable`, `corollaryC2_fullRank`, `corollaryC2`, `corollaryC3_lower`,
`corollaryC3_upper` (see `docs/open-holes.md`).
-/

universe u v

namespace GeneralizedStaffordChallenge

/-- Theorem A' (fixed ideal). -/
theorem fixedIdeal : FixedIdealStatement.{u} :=
  fixedIdeal_proof.{u}

/-- Theorem A (fixed anchor). -/
theorem fixedAnchor : FixedAnchorStatement.{u} :=
  fixedAnchor_proof.{u}

/-- Corollary B, dimension part (Lemma 6.1). -/
theorem corollaryB_dimension : CorollaryBDimensionStatement.{u} :=
  corollaryB_dimension_proof.{u}

/-- Corollary B for Theorem A. -/
theorem corollaryB_fixedAnchor : CorollaryBFixedAnchorStatement.{u} :=
  corollaryB_fixedAnchor_proof.{u}

/-- Corollary B for Theorem A'. -/
theorem corollaryB_fixedIdeal : CorollaryBFixedIdealStatement.{u} :=
  corollaryB_fixedIdeal_proof.{u}

/-- Corollary C.1 (finite Krull dimension hypothesis). -/
theorem corollaryC1 : CorollaryC1Statement.{u, v} :=
  corollaryC1_proof.{u, v}

/-- Corollary C.1 under (H_all). -/
theorem corollaryC1_hAll : CorollaryC1HAllStatement.{u, v} :=
  corollaryC1_hAll_proof.{u, v}

/-- Corollary C.1 under (H_omega). -/
theorem corollaryC1_omega : CorollaryC1OmegaStatement.{u, v} :=
  corollaryC1_omega_proof.{u, v}

/-- Corollary C.2, prescribed form. -/
theorem corollaryC2_prescribed : CorollaryC2PrescribedStatement.{u} :=
  corollaryC2_prescribed_proof.{u}

end GeneralizedStaffordChallenge
