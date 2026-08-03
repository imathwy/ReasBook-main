module

public import Topology_Munkres_2000.Book.Definition_27_5.IsolatedPoint
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Baire.LocallyCompactRegular

public section

universe u

namespace PerfectSpace

/-- Theorem 27.7: A nonempty compact Hausdorff space with no isolated points is uncountable.
Here `PerfectSpace X` is the canonical formulation of the hypothesis that `X` has no isolated
points. -/
instance uncountable_of_compactSpace {X : Type u} [TopologicalSpace X] [Nonempty X]
    [CompactSpace X] [T2Space X] [PerfectSpace X] : Uncountable X := by
  -- Assume countability so that the closed singleton cover is countably indexed.
  rw [← not_countable_iff]
  intro hX
  letI : Countable X := hX
  -- Baire category forces one singleton in this cover to have nonempty interior.
  obtain ⟨x, hx⟩ := nonempty_interior_of_iUnion_of_closed
    (f := fun x : X ↦ ({x} : Set X)) (fun _ ↦ isClosed_singleton) (Set.iUnion_of_singleton X)
  -- Perfectness makes every singleton interior empty, contradicting that conclusion.
  rw [interior_singleton] at hx
  exact Set.not_nonempty_empty hx

end PerfectSpace
