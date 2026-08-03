module

public import Topology_Munkres_2000.Book.Definition_19_1.BoxTopology

universe u v

public section

namespace Pi

/-- The generating family `Pi.boxBasis X` is a basis for the box topology. -/
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
