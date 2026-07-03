import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling:
- primary domain: homotopy invariance and quasi-isomorphisms for homological complexes;
- sampled canonical declarations:
  `Homotopy.homologyMap_eq`,
  `HomotopyEquiv.toHomologyIso`,
  `homotopyEquivalences_le_quasiIso`,
  `HomologicalComplex.mem_quasiIso_iff`;
- best owner abstraction: `Homotopy` and `HomotopyEquiv` on `HomologicalComplex`;
- primitive data: a homotopy between two morphisms, or a homotopy equivalence;
- derived API: equality of the induced homology maps, the canonical homology isomorphism of a
  homotopy equivalence, and the resulting quasi-isomorphism property;
- source/core/bridge triage:
  `core/canonical`: `Homotopy`, `HomotopyEquiv`,
  `bridge/view`: the `QuasiIso` reformulation via `HomologicalComplex.mem_quasiIso_iff`.

No extra chapter-local wrapper is needed here: the mathematical content already lives on the
owner-side declarations for homotopies of homological complexes, and the quasi-isomorphism
statement is only a companion view.
-/

/- Lemma 12.13.11: if two morphisms of complexes in an abelian category are homotopic, then they
induce the same map on homology in every degree. The quasi-isomorphism consequence for a homotopy
equivalence is recalled below via the canonical owner-side comparison. -/
recall Homotopy.homologyMap_eq
recall HomotopyEquiv.toHomologyIso

/- The quasi-isomorphism consequence of a homotopy equivalence is the owner-side comparison
`homotopyEquivalences_le_quasiIso`; the source-facing `QuasiIso` formulation is obtained by
rewriting with `HomologicalComplex.mem_quasiIso_iff`. -/
recall homotopyEquivalences_le_quasiIso
recall HomologicalComplex.mem_quasiIso_iff
