import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Definition_21_17_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_59_4

-- Declarations for this item will be appended below by the statement pipeline.

namespace SheafOfModules.RingedSite

/- Domain-style sampling pass:
- primary domain: K-flat cochain complexes of `𝒪`-modules on a ringed site and closure of
  K-flatness under totalized tensor products;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `CochainComplex.tensorObj_isKFlat_of_isKFlat`,
  `HomologicalComplex.tensorObj`;
- best owner abstraction: the ambient module category should use the chapter owner
  `ringedSiteModuleCategory`, while K-flatness itself is owned by the predicate `K.IsKFlat`
  on cochain complexes, and the tensor product complex is the canonical derived object
  `HomologicalComplex.tensorObj K L`;
- primitive vs derived: the primitive data are only the complexes `K`, `L` and their K-flatness
  hypotheses. The tensor product complex is derived from the ambient monoidal structure, so this
  ringed-site file should expose only the specialization of the owner theorem rather than a
  parallel local statement.

Source/core/bridge triage:
- `source-facing`: the ringed-site specialization of the tensor-closure statement for K-flat
  complexes;
- `core/canonical`: `CochainComplex.tensorObj_isKFlat_of_isKFlat`;
- `bridge/view`: specialization of that owner theorem to `SheafOfModules.RingedSite`. -/

/- Lemma 21.17.5: if `K` and `L` are K-flat cochain complexes of `𝒪`-modules on a ringed site
`(C, 𝒪)`, then the totalized tensor product `Tot(K ⊗ L)` is K-flat. This is exactly the
specialization of the canonical owner theorem `CochainComplex.tensorObj_isKFlat_of_isKFlat` to
`ringedSiteModuleCategory J 𝒪`. -/
recall CochainComplex.tensorObj_isKFlat_of_isKFlat

end SheafOfModules.RingedSite
