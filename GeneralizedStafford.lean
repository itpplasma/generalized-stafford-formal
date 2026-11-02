module

public import GeneralizedStafford.Basic
public import GeneralizedStafford.Germs
public import GeneralizedStafford.Descent
public import GeneralizedStafford.TheoremA
public import GeneralizedStafford.CorollaryB
public import GeneralizedStafford.Modules
public import GeneralizedStafford.GeneratorBounds

@[expose] public section

/-!
# Affine generation over simple Noetherian rings with infinite centre

Theorem A' (fixed ideal), Theorem A (fixed anchor), Corollary B, and Corollaries
C.1, C.1 (stable form), C.2 and C.3, for simple right Noetherian rings with an
infinite central field; zero divisors are allowed.

* `GeneralizedStafford.Basic`: conventions and deviation facts.
* `GeneralizedStafford.Germs`: germs, central scalars and source selection.
* `GeneralizedStafford.Descent`: the two-call descent, proving Theorem A'.
* `GeneralizedStafford.TheoremA`: Theorems A' and A.
* `GeneralizedStafford.CorollaryB`: Corollary B.
* `GeneralizedStafford.Modules`: Corollary C.1, C.1 stable form, C.2.
* `GeneralizedStafford.GeneratorBounds`: Corollary C.3, generator bounds by the
  normalized Goldie rank.
-/
