module

public import Topology_Munkres_2000.Book.Definition_58_3.HomotopyType
public import Mathlib.Topology.Category.TopCat.Basic

public section

universe u

/- Proposition 58.1: homotopy equivalences compose, and their underlying maps compose
pointwise. -/
#check ContinuousMap.HomotopyEquiv.trans
#check ContinuousMap.HomotopyEquiv.trans_apply

/-- Proposition 58.1: having the same homotopy type is an equivalence relation on topological
spaces. -/
theorem sameHomotopyType_equivalence :
    Equivalence (fun X Y : TopCat.{u} ↦ SameHomotopyType X Y) :=
  ⟨fun X ↦ SameHomotopyType.refl X,
    fun {_ _} h ↦ h.symm,
    fun {_ _ _} hXY hYZ ↦ hXY.trans hYZ⟩
