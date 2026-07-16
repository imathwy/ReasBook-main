import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap10.Definition_10_72_1
import StacksProject_2024.stacks_project.Chap10.«Lemma_10_119_2_Kollár»

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing

section

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-
Domain-style sampling:
- primary domain: commutative algebra of local Noetherian rings, organized around the chapter-local
  depth owner `moduleDepth` and the exceptional finite-extension alternative in Kollár's lemma;
- sampled owner API: `Ideal.depth`, `moduleDepth`, `HasKollarExceptionalFiniteExtension`,
  `kollar_exactly_one_of_artinian_regular_dim_one_depth_ge_two_or_exceptional_finite_extension`;
- layer: `bridge/view`, since this file is only a duplicate presentation of owner declarations
  already introduced canonically elsewhere in the chapter.

Primitive data are already owned upstream: local depth is derived from `Ideal.depth`, and the
fourth alternative is the existing proposition `HasKollarExceptionalFiniteExtension R`. This file
therefore reuses those owners directly instead of keeping parallel duplicate definitions; the main
recalled theorem now also exposes its third branch at the canonical local-depth interface
`moduleDepth R R`.
-/

/- The local depth notion used in Kollár's lemma is the chapter owner `moduleDepth`, i.e. the
maximal-ideal specialization of `Ideal.depth`. -/
recall moduleDepth

/- Kollár's fourth alternative is already the canonical owner declaration
`HasKollarExceptionalFiniteExtension R`. -/
recall HasKollarExceptionalFiniteExtension

/- The unpacking theorem for the exceptional finite-extension alternative is already owned by the
canonical companion theorem. -/
recall hasKollarExceptionalFiniteExtension_iff

variable [IsNoetherianRing R]

/- Lemma 10.119.2 (Koll_r) is exactly the chapter-local canonical theorem already recorded in the
owner file `Lemma_10_119_2_Kollár`. -/
recall kollar_exactly_one_of_artinian_regular_dim_one_depth_ge_two_or_exceptional_finite_extension

end
