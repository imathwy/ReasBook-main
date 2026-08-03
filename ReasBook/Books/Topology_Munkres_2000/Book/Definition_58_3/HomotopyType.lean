module

public import Topology_Munkres_2000.Book.Definition_58_2

public section

open scoped ContinuousMap

universe u v w

/-- Two topological spaces have the same homotopy type if there exists a homotopy equivalence
between them. -/
def SameHomotopyType (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] : Prop :=
  Nonempty (X ≃ₕ Y)

namespace SameHomotopyType

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A homotopy equivalence exhibits its source and target as having the same homotopy type. -/
theorem ofHomotopyEquiv (e : X ≃ₕ Y) : SameHomotopyType X Y := ⟨e⟩

/-- Every topological space has the same homotopy type as itself. -/
protected theorem refl (X : Type u) [TopologicalSpace X] : SameHomotopyType X X :=
  ofHomotopyEquiv (.refl X)

/-- Having the same homotopy type is symmetric. -/
protected theorem symm (h : SameHomotopyType X Y) : SameHomotopyType Y X :=
  h.map ContinuousMap.HomotopyEquiv.symm

/-- Having the same homotopy type is transitive. -/
protected theorem trans (hXY : SameHomotopyType X Y) (hYZ : SameHomotopyType Y Z) :
    SameHomotopyType X Z :=
  Nonempty.map2 ContinuousMap.HomotopyEquiv.trans hXY hYZ

/-- Having the same homotopy type means admitting a homotopy equivalence. -/
theorem iff_nonempty_homotopyEquiv : SameHomotopyType X Y ↔ Nonempty (X ≃ₕ Y) := Iff.rfl

end SameHomotopyType
