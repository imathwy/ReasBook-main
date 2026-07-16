import Mathlib.Topology.Sets.Opens
import StacksProject_2024.stacks_project.Chap05.Definition_5_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace

universe u v

section

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for basis refinements:
- owner abstraction: `TopologicalSpace.IsTopologicalBasis`
- same-domain declarations inspected:
  `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`,
  `TopologicalSpace.IsTopologicalBasis.open_eq_iUnion`,
  `TopologicalSpace.IsTopologicalBasis.open_eq_sUnion`,
  `Definition_5_5_1`

Layer triage:
- `source-facing`: a refinement statement for an indexed open cover of an open subset
- `core/canonical`: `TopologicalSpace.IsTopologicalBasis`
- `bridge/view`: the resulting indexed refining family of opens, each carried by a basis member

Primitive data is the basis owner `hB` together with the indexed open family `Ui` covering `U`.
The refining family should therefore be returned directly as basis members `V j ∈ B`, obtained by
applying the owner theorem `hB.open_eq_iUnion` to each member of the cover. The openness of each
`V j` is derived from `hB.isOpen`, so bundling those sets again as `Opens X` would only duplicate
owner data instead of exposing the source-facing refinement.
-/

/-- Lemma 5.5.3: every indexed open cover `U = ⋃ i Ui i` admits a refinement by members of the
basis `B`. -/
-- Proof sketch: apply `hB.open_eq_iUnion` to each open set `Ui i`, then reindex the resulting
-- basis decompositions by a sigma type to obtain a basis-member refinement of the original cover.
theorem exists_basis_refinement_of_cover
    {ι : Type v} (B : Set (Set X)) (hB : IsTopologicalBasis B)
    (U : Opens X) (Ui : ι → Opens X) (hUi : (U : Set X) = ⋃ i, (Ui i : Set X)) :
    ∃ (J : Type (max u v)) (V : J → {V : Set X // V ∈ B}),
      (U : Set X) = ⋃ j, (V j : Set X) ∧ ∀ j, ∃ i, (V j : Set X) ⊆ Ui i := sorry

end
