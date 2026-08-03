module

public import Topology_Munkres_2000.Book.Proposition_58_1

public section

universe u

/-- Exercise 58.3: homotopy equivalence is an equivalence relation on any collection of
topological spaces. -/
theorem sameHomotopyType_equivalenceOn (C : Set TopCat.{u}) :
    Equivalence (fun X Y : C ↦ SameHomotopyType X Y) :=
  sameHomotopyType_equivalence.comap Subtype.val
