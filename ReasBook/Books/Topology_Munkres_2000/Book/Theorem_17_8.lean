module

public import Topology_Munkres_2000.Book.Definition_17_5

public section

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]

/- Theorem 17.8: Every finite point set in a Hausdorff space `X` is closed. -/
#check fun {s : Set X} (hs : s.Finite) ↦ hs.isClosed
