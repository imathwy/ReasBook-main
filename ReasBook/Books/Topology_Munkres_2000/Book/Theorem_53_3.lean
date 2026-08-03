module

public import Topology_Munkres_2000.Book.Definition_53_2.Covering
public import Topology_Munkres_2000.Book.Theorem_53_3.Product

public section

universe u₁ u₂ v₁ v₂

/-- Theorem 53.3. If `p : E → B` and `p' : E' → B'` are covering maps in Munkres'
surjective convention, then their product map `Prod.map p p' : E × E' → B × B'` is
a covering map in the same convention. -/
theorem IsSurjectiveCoveringMap.prodMap {E : Type u₁} {B : Type u₂}
    {E' : Type v₁} {B' : Type v₂}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
    {p : E → B} {p' : E' → B'} (hp : IsSurjectiveCoveringMap p)
    (hp' : IsSurjectiveCoveringMap p') :
    IsSurjectiveCoveringMap (Prod.map p p') := by
  -- Combine the product covering model with surjectivity in each coordinate.
  exact (isSurjectiveCoveringMap_iff _).2
    ⟨hp.isCoveringMap.prodMap hp'.isCoveringMap, hp.surjective.prodMap hp'.surjective⟩

end
