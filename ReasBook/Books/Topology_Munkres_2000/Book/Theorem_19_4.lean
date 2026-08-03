module

public import Topology_Munkres_2000.Book.Definition_19_1.BoxTopology
public import Mathlib.Topology.Separation.Hausdorff

import Topology_Munkres_2000.Book.Proposition_19_3.Comparison
import Mathlib.Topology.WithTopology

public section

universe u v

namespace Pi

/-- A dependent product equipped with the box topology. -/
abbrev BoxProduct {ι : Type u} (X : ι → Type v)
    [(i : ι) → TopologicalSpace (X i)] :=
  WithTopology ((i : ι) → X i) (boxTopologicalSpace X)

/-- Theorem 19.4: A dependent product of Hausdorff spaces is Hausdorff in the box topology. -/
instance instT2SpaceBoxProduct {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] [(i : ι) → T2Space (X i)] :
    T2Space (BoxProduct X) := by
  -- Transfer product Hausdorffness to the finer raw box topology.
  have rawBoxT2Space : @T2Space ((i : ι) → X i) (boxTopologicalSpace X) :=
    t2Space_antitone box_le_product Pi.t2Space
  -- Transport separation across the canonical boxed wrapper.
  exact @T2Space.of_injective_continuous
    (BoxProduct X) ((i : ι) → X i)
    inferInstance (boxTopologicalSpace X) rawBoxT2Space
    (WithTopology.ofTopology (t := boxTopologicalSpace X))
    (WithTopology.ofTopology_injective (boxTopologicalSpace X))
    (WithTopology.continuous_ofTopology (boxTopologicalSpace X))

end Pi

/- Theorem 19.4 (2): A dependent product of Hausdorff spaces is Hausdorff in the
product topology. -/
#check Pi.t2Space
