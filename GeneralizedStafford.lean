module

public import GeneralizedStafford.Basic
public import GeneralizedStafford.Germs
public import GeneralizedStafford.Descent
public import GeneralizedStafford.TheoremA
public import GeneralizedStafford.CorollaryB
public import GeneralizedStafford.Modules

@[expose] public section

/-!
# Affine generation over simple Noetherian rings with infinite centre

Theorem A' (fixed ideal), Theorem A (fixed anchor), Corollary B and
Corollary C.1, C.1 stable and C.2 of `docs/core-theorem.md`, for simple right
Noetherian rings with an infinite central field; zero divisors are allowed.

* `GeneralizedStafford.Basic`: conventions and deviation facts (Section 0).
* `GeneralizedStafford.Germs`: germs and source selection (Section 3).
* `GeneralizedStafford.Descent`: the two-call descent (Section 4).
* `GeneralizedStafford.TheoremA`: Theorems A' and A (Section 1).
* `GeneralizedStafford.CorollaryB`: Corollary B (Lemma 6.1).
* `GeneralizedStafford.Modules`: Corollary C.1, C.1 stable, C.2
  (Lemmas 6.2, 6.3).
-/
