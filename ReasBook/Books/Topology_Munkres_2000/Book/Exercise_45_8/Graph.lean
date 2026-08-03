module

public import Mathlib.Data.Rel
import Mathlib.Data.Set.Prod
public import Mathlib.Topology.Bornology.Constructions

public section

open Set

namespace Function

/-- A function graph is bounded exactly when its domain and range are bounded. -/
theorem graph_isBounded_iff {X : Type u} {Y : Type v} [Bornology X] [Bornology Y]
    (f : X → Y) :
    Bornology.IsBounded (graph f) ↔
      Bornology.IsBounded (Set.univ : Set X) ∧ Bornology.IsBounded (Set.range f) := by
  have hgraph : graph f = Set.univ.graphOn f := by
    ext x
    simp [graph]
  rw [hgraph, ← Bornology.isBounded_image_fst_and_snd, Set.image_fst_graphOn]
  simp

end Function
