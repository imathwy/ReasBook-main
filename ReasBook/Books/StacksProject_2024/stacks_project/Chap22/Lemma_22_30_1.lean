import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap22.Lemma_22_26_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DifferentialGradedCategory

universe u v w

-- Source/core/bridge triage:
-- * source-facing: the displayed internal-Hom functor on differential graded modules attached to a
--   bimodule `N`;
-- * core/canonical: the Chapter 22 DG functor owner `homOverBFromN`;
-- * bridge/view: the induced ordinary and homotopy-category functors
--   `homOverBFromN.mapComp` and `homOverBFromN.mapK`.

/- Companion recalls: Lemma `22.26.5` already exports the canonical DG-functor-to-underlying-
category bridges `DgFunctor.mapComp` and `DgFunctor.mapK`, so Lemma `22.30.1` should reuse them
directly rather than introduce local aliases. -/
recall DgFunctor.mapComp
recall DgFunctor.mapK

section

variable {R : Type u} [CommRing R]
variable {DGModB : Type v} {DGModA : Type w}
variable [DifferentialGradedCategory R DGModB] [DifferentialGradedCategory R DGModA]
variable (homOverBFromN : DgFunctor R DGModB DGModA)

-- Semantic recall hit: `lean_leansearch` surfaced the generic homotopy-category transport
-- `Functor.mapHomotopyCategory`; local Chapter 22 inspection shows that this item is already
-- owned more faithfully by the project-local DG-category functor constructions
-- `DgFunctor.mapComp` and `DgFunctor.mapK`.

/- Lemma 22.30.1: once the internal-Hom construction attached to a differential graded
`(A, B)`-bimodule `N` has been formalized as a DG functor
`homOverBFromN : DgFunctor R DGModB DGModA`, the induced functor on the underlying categories of
differential graded modules is the canonical owner `homOverBFromN.mapComp`, and the induced
functor on homotopy categories is the canonical owner `homOverBFromN.mapK`.

This file is therefore recall-only: introducing local aliases would duplicate the exact interface
already exported by Lemma `22.26.5`. -/
#check homOverBFromN
#check (homOverBFromN.mapComp : Comp R DGModB ⥤ Comp R DGModA)
#check (homOverBFromN.mapK : K R DGModB ⥤ K R DGModA)

end
