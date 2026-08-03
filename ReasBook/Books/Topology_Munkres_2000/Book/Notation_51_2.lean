module

public import Topology_Munkres_2000.Book.Notation_51_2.HomotopyClass

public section

universe u v

notation "⟦" X ", " Y "⟧ₕ" => ContinuousMap.Homotopic.Quotient X Y

variable (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]

/- Notation 51.2: Given topological spaces `X` and `Y`, `⟦X, Y⟧ₕ` denotes the
type of ordinary homotopy classes of continuous maps from `X` to `Y`. -/
#check ⟦X, Y⟧ₕ
