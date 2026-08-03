module

public import Topology_Munkres_2000.Book.Definition_66_1.WindingNumber
public import Topology_Munkres_2000.Book.Exercise_66_1.LoopQuotient

noncomputable section

public section

open Set

namespace PlaneLoop

/-- The circle map induced by the normalized direction loop of a plane loop avoiding `a`. -/
def normalizedCircleMap {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) : C(Circle, Circle) :=
  (normalizedLoop f a h_avoid).toCircleMap

/-- Pulling the normalized circle map back to the interval gives the normalized loop. -/
theorem normalizedCircleMap_comp {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) :
    (normalizedCircleMap f a h_avoid).comp Circle.intervalQuotient =
      (normalizedLoop f a h_avoid).toContinuousMap := by
  -- This is the defining pullback property of the descended loop map.
  exact Path.toCircleMap_comp (normalizedLoop f a h_avoid)

end PlaneLoop
