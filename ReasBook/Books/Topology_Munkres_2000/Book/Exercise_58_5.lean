module

public import Topology_Munkres_2000.Book.Definition_58_3.HomotopyType
public import Mathlib.Topology.Homotopy.Contractible

public section

universe u

/-- Exercise 58.5: The identity map of `X` is nullhomotopic if and only if `X`
has the homotopy type of the one-point space `Unit`. -/
theorem id_nullhomotopic_iff_sameHomotopyType_unit (X : Type u) [TopologicalSpace X] :
    (ContinuousMap.id X).Nullhomotopic ↔ SameHomotopyType X Unit := by
  rw [← contractible_iff_id_nullhomotopic]
  exact
    ⟨fun h ↦ SameHomotopyType.iff_nonempty_homotopyEquiv.mpr h.hequiv_unit',
      fun h ↦ ContractibleSpace.mk (SameHomotopyType.iff_nonempty_homotopyEquiv.mp h)⟩
