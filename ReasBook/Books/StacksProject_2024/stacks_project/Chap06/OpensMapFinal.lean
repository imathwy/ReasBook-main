import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.IsConnected
import Mathlib.Topology.Category.TopCat.Opens

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace TopologicalSpace.Opens

instance map_final {X Y : TopCat.{u}} (f : X ⟶ Y) :
    Functor.Final (Opens.map f) where
  out U := by
    let T : StructuredArrow U (Opens.map f) := StructuredArrow.mk (Opens.leMapTop f U)
    have hT : IsTerminal T := by
      refine IsTerminal.ofUniqueHom
        (fun A ↦
          StructuredArrow.homMk
            (homOfLE (show A.right ≤ (⊤ : Opens Y) from fun _ _ ↦ trivial))
            (by subsingleton))
        ?_
      intro A m
      apply StructuredArrow.ext
      subsingleton
    exact isConnected_of_isTerminal (StructuredArrow U (Opens.map f)) hT

end TopologicalSpace.Opens
