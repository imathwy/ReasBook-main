import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory HomologicalComplex

universe v u

variable {ι : Type v} {V : Type u} [Category.{v} V] [Preadditive V] {c : ComplexShape ι}

/- Domain-style sampling for Definition 12.13.8:
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
two homotopies from the composites to the identities. The morphism-property formulation
`homotopyEquivalences` is derived API from that owner, so the present item should recall only that
canonical source-facing bridge rather than duplicating the owner entry from Definition 12.13.2.
-/

/- Definition 12.13.8: for complexes in an additive category, the property that a morphism is a
homotopy equivalence is the canonical morphism property
`HomologicalComplex.homotopyEquivalences`. -/
recall HomologicalComplex.homotopyEquivalences
