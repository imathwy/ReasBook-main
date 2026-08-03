module

public import Topology_Munkres_2000.Book.Example_53_1.Projection

/-! Exercises for §53, covering spaces. -/

public section

universe u v

/-- Exercise 53.1. If `Y` is nonempty and has the discrete topology, then projection onto the
first coordinate is a covering map in Munkres's surjective sense. -/
theorem isCoveringMap_fst_surjective (X : Type u) (Y : Type v) [TopologicalSpace X]
    [TopologicalSpace Y] [DiscreteTopology Y] [Nonempty Y] :
    IsCoveringMap (Prod.fst : X × Y → X) ∧ Function.Surjective (Prod.fst : X × Y → X) :=
  ⟨isCoveringMap_fst X Y, Prod.fst_surjective⟩
