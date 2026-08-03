module

public import Topology_Munkres_2000.Book.Exercise_25_1.Connectedness
public import Topology_Munkres_2000.Book.Definition_25_2

public section

open Set

namespace SorgenfreyLine

/- Exercise 25.1 (1): Every connected component of the Sorgenfrey line is a singleton. -/
#check (connectedComponent_eq_singleton : ∀ x : SorgenfreyLine, connectedComponent x = {x})

/-- The path-component answer for Exercise 25.1: every path component of the Sorgenfrey line is a
singleton. -/
theorem pathComponent_eq_singleton (x : SorgenfreyLine) :
    pathComponent x = ({x} : Set SorgenfreyLine) := by
  -- A path component lies in the connected component, which is already known to be a singleton.
  apply Set.Subset.antisymm
  · rw [← connectedComponent_eq_singleton x]
    exact pathComponent_subset_component x
  -- The base point always belongs to its own path component.
  · rw [singleton_subset_iff]
    exact mem_pathComponent_self x

/-- Exercise 25.1 (3): A map from the usual real line to the Sorgenfrey line is
continuous exactly when it is constant. -/
theorem continuous_iff_constant (f : ℝ → SorgenfreyLine) :
    Continuous f ↔ ∀ x y : ℝ, f x = f y := by
  constructor
  -- A continuous image of the connected real line in a totally disconnected space is a point.
  · intro hf x y
    exact TotallyDisconnectedSpace.eq_of_continuous f hf x y
  -- Pairwise equality rewrites the map as a constant map, which is continuous.
  · intro h
    have hconstant : f = fun _ ↦ f 0 := funext fun x ↦ h x 0
    rw [hconstant]
    exact continuous_const

end SorgenfreyLine
