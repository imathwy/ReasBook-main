module

public import Topology_Munkres_2000.Book.Exercise_51_3.Contractible
public import Topology_Munkres_2000.Book.Notation_51_2

public section

universe u v

open ContinuousMap.Homotopic.Quotient

/-- Exercise 51.2 (a): For every space `X`, the type `⟦X, unitInterval⟧ₕ` has exactly one
element. -/
instance uniqueHomotopyClassIntoUnitInterval {X : Type u} [TopologicalSpace X] :
    Unique ⟦X, unitInterval⟧ₕ where
  default := mk (ContinuousMap.const X 0)
  uniq _ := Subsingleton.elim _ _

/-- Exercise 51.2 (b): If `Y` is path-connected, the type `⟦unitInterval, Y⟧ₕ` has exactly one
element. -/
noncomputable instance uniqueHomotopyClassFromUnitInterval {Y : Type v} [TopologicalSpace Y]
    [PathConnectedSpace Y] : Unique ⟦unitInterval, Y⟧ₕ where
  default := mk (ContinuousMap.const unitInterval (Classical.choice PathConnectedSpace.nonempty))
  uniq _ := Subsingleton.elim _ _
