import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory HomologicalComplex

universe v u

variable {ι : Type v} {V : Type u} [Category.{v} V] [Preadditive V] {c : ComplexShape ι}

/- Domain-style sampling for Lemma 12.13.1:
- primary domain: homotopies of homological complexes in a preadditive category;
- sampled canonical owner declarations:
  `Homotopy`,
  `Homotopy.compLeft`,
  `Homotopy.compRight`,
  `Homotopy.comp`;
- best owner abstraction: `Homotopy` on `HomologicalComplex V c`;
- primitive data: the fields `hom`, `zero`, and `comm` of a homotopy;
- derived API: closure under precomposition and postcomposition, together with the degreewise
  component lemmas `Homotopy.compLeft_hom` and `Homotopy.compRight_hom`;
- source/core/bridge triage:
  `core/canonical`: `Homotopy` and its composition operations on `HomologicalComplex`.

This item is already owner-side mathematics, so the refined file should recall the canonical
declarations directly rather than introduce a chapter-local duplicate wrapper or alias.
-/

/- Lemma 12.13.1: the owner abstraction `Homotopy` is closed under precomposition and
postcomposition by morphisms of chain complexes, via the canonical operations
`Homotopy.compLeft` and `Homotopy.compRight`. -/
recall Homotopy.compLeft
recall Homotopy.compRight

/- The degreewise formulas for these owner operations are already the canonical component lemmas
`Homotopy.compLeft_hom` and `Homotopy.compRight_hom`. -/
recall Homotopy.compLeft_hom
recall Homotopy.compRight_hom
