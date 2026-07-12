import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory HomologicalComplex

universe v u

variable {V : Type u} [Category.{v} V] [Abelian V]

/- Domain-style sampling:
- primary domain: homotopy invariance and quasi-isomorphisms for homological complexes
- core/canonical owner abstraction: `Homotopy` and `HomotopyEquiv` on `HomologicalComplex`
- primitive data: a homotopy between morphisms, or a homotopy equivalence
- derived API: equality of induced homology maps, the canonical homology isomorphism of a
  homotopy equivalence, and the quasi-isomorphism consequence
- source-facing layer here: the `ChainComplex V ℤ` specialization
- bridge/view layer: rewriting the owner-side morphism-property statement via `mem_quasiIso_iff`
-/

/- Lemma 12.13.5: homotopic maps of chain complexes in an abelian category induce the same maps
on homology. This is exactly the owner theorem `Homotopy.homologyMap_eq`, specialized to
`ChainComplex V ℤ`. -/
recall Homotopy.homologyMap_eq
recall HomotopyEquiv.toHomologyIso

/- The quasi-isomorphism consequence for a homotopy equivalence is the owner-side comparison
`homotopyEquivalences_le_quasiIso`; for chain complexes, the source-facing `QuasiIso`
formulation is obtained by rewriting with `mem_quasiIso_iff`. -/
recall homotopyEquivalences_le_quasiIso
recall mem_quasiIso_iff
