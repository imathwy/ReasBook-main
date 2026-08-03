module

public import Topology_Munkres_2000.Book.Definition_19_1.BoxTopology
public import Mathlib.Topology.Bases

public section

universe u v

namespace Pi

/-- Theorem 19.1 (1): the full boxes `∏ i, U i`, with every `U i` open in
`X i`, form a basis for the box topology on `(i : ι) → X i`. -/
theorem isTopologicalBasis_boxBasis {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] :
    (boxTopologicalSpace X).IsTopologicalBasis (boxBasis X) := by
  -- Fix the generated box topology as the ambient topology for the basis API.
  letI : TopologicalSpace ((i : ι) → X i) := boxTopologicalSpace X
  -- View the box topology through its defining generated topology.
  have hGenerated :
      boxTopologicalSpace X = TopologicalSpace.generateFrom (boxBasis X) := rfl
  -- Intersection closure makes the generators together with `univ` a basis.
  have hWithUniv := TopologicalSpace.isTopologicalBasis_of_subbasis_of_inter hGenerated
    (fun _ hs _ ht ↦ inter_mem_boxBasis hs ht)
  -- Since the full product is already a box, the inserted set is redundant.
  simpa only [Set.insert_eq_of_mem (univ_mem_boxBasis X)] using hWithUniv

end Pi

/- Theorem 19.1 (2): finite-coordinate open cylinders form a basis for the product
topology on `(i : ι) → X i`. Such a cylinder is equivalently a full box whose
coordinate set is `Set.univ` outside a finite set of indices. -/
#check fun {ι : Type u} {X : ι → Type v} [(i : ι) → TopologicalSpace (X i)] ↦
  isTopologicalBasis_pi (fun _ ↦ TopologicalSpace.isTopologicalBasis_opens)
