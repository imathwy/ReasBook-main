module

public import Mathlib.Topology.Homotopy.Equiv
public import Topology_Munkres_2000.Book.Lemma_58_4
import Topology_Munkres_2000.Book.Theorem_52_4.Functoriality

public section

open scoped ContinuousMap

universe u v

namespace ContinuousMap.HomotopyEquiv

open FundamentalGroup.LeftToRight

/-- Remark 58.1. Although `e.symm` is a homotopy inverse of `e`, its induced map
is not literally the inverse of the map induced by `e`: their composite changes
basepoint along the path traced by the inverse homotopy. -/
theorem fundamentalGroupMap_comp_eq_basepointChange {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (x₀ : X) :
    ∃ α : Path x₀ (e.symm (e x₀)),
      (e.symm.toFun₍(e x₀)₎)₊.comp (e.toFun₍x₀₎)₊ =
        (mulEquivOfPath α).toMonoidHom := by
  -- The inverse homotopy traces the path along which the basepoint changes.
  obtain ⟨α, map_eq⟩ :=
    FundamentalGroup.exists_path_map_eq_basepointChange_comp_of_homotopic
      (ContinuousMap.id X) (e.symm.toFun.comp e.toFun) x₀ e.left_inv.symm
  refine ⟨α, ?_⟩
  -- Functoriality identifies the displayed composite, while the identity factor vanishes.
  rw [← map_comp]
  rw [map_id] at map_eq
  exact map_eq.trans (MonoidHom.comp_id _)

end ContinuousMap.HomotopyEquiv

end
