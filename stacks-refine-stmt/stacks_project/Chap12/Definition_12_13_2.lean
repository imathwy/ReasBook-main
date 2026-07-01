import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

open CategoryTheory HomologicalComplex

variable {ι : Type v} {V : Type u} [Category.{v} V] [Preadditive V] {c : ComplexShape ι}

/- Domain-style sampling for Definition 12.13.2:
- primary domain: homotopy equivalences of homological complexes in a preadditive category;
- sampled canonical declarations:
  `HomotopyEquiv`,
  `HomologicalComplex.homotopyEquivalences`,
  `HomotopyEquiv.ofIso`,
  `HomotopyEquiv.trans`;
- source/core/bridge triage:
  `core/canonical`: `HomotopyEquiv A B`,
  `bridge/view`: `homotopyEquivalences V c a`.

The primitive data are already owned by `HomotopyEquiv`: a forward map, a backward map, and the
two homotopies exhibiting the composites as homotopic to the identities. The morphism-property
formulation `homotopyEquivalences` is derived from that owner and should remain a bridge/view,
not a parallel chapter-local notion.
-/

/- Definition 12.13.2: the owner notion that two complexes in an additive category are homotopy
equivalent is the canonical structure `HomotopyEquiv`; the associated morphism property is
`homotopyEquivalences`. -/
recall HomotopyEquiv
recall HomologicalComplex.homotopyEquivalences
