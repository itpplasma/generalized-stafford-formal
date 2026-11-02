# Literature

The classical sources behind the formal proof, and the Lean modules that use
them. Paths starting with `AlgebraicAnalysis/` are in the pinned
[AlgebraicAnalysis](https://github.com/itpplasma/algebraic-analysis) library;
the others are in this repository. This index makes no novelty or priority
claim; literature that was not found is not evidence of originality.
Item numbers in [MR] follow the research note, which marks them as still to be
checked against the book.

## Sources used by the proof

| Ingredient | Source | Lean modules |
| --- | --- | --- |
| Right Gabriel-Rentschler (deviation) dimension; `Kdim` of exact sequences; Noetherian modules have `Kdim` | [GR67]; [MR] 6.1, 6.2.3 | `AlgebraicAnalysis/Module/Deviation.lean`, `AlgebraicAnalysis/Module/DeviationOmega.lean`; inline `PosetDevLE` in the challenge |
| Critical modules and critical filtrations | [GoR73]; [MR] 6.2.10 | `AlgebraicAnalysis/Module/Critical.lean`, `AlgebraicAnalysis/Module/CriticalFiltration.lean` |
| Gabriel quotient by `Kdim < e` and finite top strata (core I2, I3), represented by germs | [Gab62] Ch. III; [Rob76]; [GoR73] | `AlgebraicAnalysis/Module/Germ.lean`, `AlgebraicAnalysis/Module/GermSchur.lean`, `AlgebraicAnalysis/Module/DualSeparationGeneral.lean`; `GeneralizedStafford/Germs.lean` |
| Linear algebra over the Schur division ring; central pencils (core I4) | standard | `AlgebraicAnalysis/Module/TorsionEscape.lean`; `GeneralizedStafford/Germs.lean` |
| Goldie's theorem for simple right Noetherian rings: regular elements form a right Ore set; Goldie torsion; common regular annihilators; elements of full rank (core I1) | [Gol58], [Gol60]; [MR] 2.1, 2.3 | `AlgebraicAnalysis/RingTheory/Goldie/Basic.lean`, `AlgebraicAnalysis/RingTheory/Goldie/Torsion.lean`; `GeneralizedStafford/Descent.lean`, `GeneralizedStafford/Modules.lean` |
| Classical right quotient ring `Q = M_s(D)` (Wedderburn-Artin from Mathlib) | [Gol58]; [MR] 2.3 | `AlgebraicAnalysis/RingTheory/Goldie/QuotientRing.lean` |
| Uniform dimension; Ore localization of modules and its exactness; Goldie rank `length_Q(M ⊗ Q)` (C.3) | [MR] 2.2, 2.3; Goodearl-Warfield, Ch. 5 (cited in AlgebraicAnalysis) | `AlgebraicAnalysis/Module/UniformDimension.lean`, `AlgebraicAnalysis/Ore/ModuleLocalization.lean`, `AlgebraicAnalysis/RingTheory/Goldie/Rank.lean`, `AlgebraicAnalysis/RingTheory/Goldie/Idempotents.lean`; the C.3 module of this repository |

The two-call descent (`GeneralizedStafford/Descent.lean`), its assembly into
Theorems A' and A (`GeneralizedStafford/TheoremA.lean`) and the corollary
proofs (`GeneralizedStafford/CorollaryB.lean`, `GeneralizedStafford/Modules.lean`
and the C.3 module) follow the research note `docs/core-theorem.md` and, for
the C.3 upper bound, `docs/lane-C3-rank-without-morita.md`.

## Context

These works state the problem or related results. No Lean module depends on
them.

| Topic | Source |
| --- | --- |
| Two-generation of right ideals of Weyl algebras, the relative form (Thm 3.1), stable two-generation of torsion modules (Thm 3.7) and Conjecture 3.8, `A_n = dA_n + fdA_n` | [Sta78] |
| Prescribed-tail generation of Artinian modules over simple Noetherian rings | [Sta82] Prop. 1.3; [Sta78b] Thm 5.1 |
| `(n+1)`-generation of right ideals; stable range; generator bounds for torsion modules | [Sta76] Cor. 1.5; [Sta77]; [Sta81] Thm 3.1, Cor. 3.7; [Cou91] Cor. 8.5 |
| Two-generation for rings of differential operators; three generators suffice | [Bjo81] Problem 2.10; [CH88] |
| Survey and open questions | [Bel26]; [CL10] |

## Bibliography

- [Bel26] G. Bellamy, Module structure of Weyl algebras, J. London Math. Soc. (2) 113 (2026), e70373. doi:10.1112/jlms.70373
- [Bjo81] J.-E. Björk, The Bernstein class of modules on algebraic manifolds, Lecture Notes in Math. 867, Springer (1981), 148-156.
- [CH88] S. C. Coutinho and M. P. Holland, Module structure of rings of differential operators, Proc. London Math. Soc. (3) 57 (1988), 417-432.
- [CL10] N. Caro and D. Levcovitz, On a theorem of Stafford, preprint (2010).
- [Cou91] S. C. Coutinho, Basic element theory of noncommutative Noetherian rings, J. Algebra 144 (1991), 24-42.
- [Gab62] P. Gabriel, Des catégories abéliennes, Bull. Soc. Math. France 90 (1962), 323-448.
- [GR67] P. Gabriel and R. Rentschler, Sur la dimension des anneaux et ensembles ordonnés, C. R. Acad. Sci. Paris Sér. A-B 265 (1967), A712-A715.
- [Gol58] A. W. Goldie, The structure of prime rings under ascending chain conditions, Proc. London Math. Soc. (3) 8 (1958), 589-608.
- [Gol60] A. W. Goldie, Semi-prime rings with maximum condition, Proc. London Math. Soc. (3) 10 (1960), 201-220.
- [GoR73] R. Gordon and J. C. Robson, Krull dimension, Mem. Amer. Math. Soc. 133 (1973).
- [MR] J. C. McConnell and J. C. Robson, Noncommutative Noetherian Rings, Grad. Stud. Math. 30, Amer. Math. Soc. (2001).
- [Rob76] J. C. Robson, Cyclic and faithful objects in quotient categories with applications to Noetherian simple or Asano rings, in: Noncommutative Ring Theory (Kent State, 1975), Lecture Notes in Math. 545, Springer (1976), 151-172.
- [Sta76] J. T. Stafford, Completely faithful modules and ideals of simple Noetherian rings, Bull. London Math. Soc. 8 (1976), 168-173.
- [Sta77] J. T. Stafford, Stable structure of noncommutative Noetherian rings, J. Algebra 47 (1977), 244-267.
- [Sta78] J. T. Stafford, Module structure of Weyl algebras, J. London Math. Soc. (2) 18 (1978), 429-442. doi:10.1112/jlms/s2-18.3.429
- [Sta78b] J. T. Stafford, Stable structure of noncommutative Noetherian rings. II, J. Algebra 52 (1978), 218-235.
- [Sta81] J. T. Stafford, Generating modules efficiently: algebraic K-theory for noncommutative Noetherian rings, J. Algebra 69 (1981), 312-346; corrigendum J. Algebra 82 (1983), 294-296.
- [Sta82] J. T. Stafford, Generating modules efficiently over noncommutative rings, Lecture Notes in Math. 924, Springer (1982), 72-88.

Bibliographic data follow the manuscript's bibliography. Entries marked there
for verification (Robson 1976, Stafford 1978b, Stafford 1982) are not yet
checked against the publications.
