module

public import Topology_Munkres_2000.Book.Exercise_29_11

public section

namespace Topology.IsQuotientMap

/-- Exercise 46.9: If `p : A → B` is a quotient map and `X` is locally compact
Hausdorff, then `Prod.map (id : X → X) p`, denoted `i_X × p` in the source, is
a quotient map. The Hausdorff hypothesis is not needed for the conclusion. -/
theorem id_prodMap {A : Type u} {B : Type v} {X : Type w}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
    [LocallyCompactSpace X] {p : A → B} (hp : IsQuotientMap p) :
    IsQuotientMap (Prod.map (id : X → X) p) := by
  rw [show Prod.map (id : X → X) p =
    (Homeomorph.prodComm B X) ∘ Prod.map p id ∘ (Homeomorph.prodComm X A) by
      funext x
      rfl]
  exact (Homeomorph.prodComm B X).isQuotientMap.comp
    (hp.prodMap_id.comp (Homeomorph.prodComm X A).isQuotientMap)

end Topology.IsQuotientMap
