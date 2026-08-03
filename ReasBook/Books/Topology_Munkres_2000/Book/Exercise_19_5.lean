module

public import Topology_Munkres_2000.Book.Exercise_19_5.Projection

public section

universe u v w

open scoped Topology

/-- Exercise 19.5: A continuous map into a dependent product with the box topology
has continuous coordinate functions. -/
theorem Continuous.box_apply {A : Type u} {ι : Type v} {X : ι → Type w}
    [TopologicalSpace A] [(i : ι) → TopologicalSpace (X i)]
    {f : A → (i : ι) → X i}
    (hf : Continuous[_, Pi.boxTopologicalSpace X] f) (i : ι) :
    Continuous fun a ↦ f a i := by
  -- Use the box topology as the intermediate topology in the composition.
  letI : TopologicalSpace ((i : ι) → X i) := Pi.boxTopologicalSpace X
  -- Compose with the continuous box-topology coordinate projection.
  exact (Pi.continuous_box_apply i).comp' hf
