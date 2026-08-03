module

public import Topology_Munkres_2000.Book.Definition_53_1
public import Topology_Munkres_2000.Book.Definition_53_2.Covering

public section

universe u v

/-- Theorem 53.2. If `p : E → B` is a covering map in Munkres' surjective
convention and `B₀` is a subspace of `B`, then the restriction of `p` from
`p ⁻¹' B₀` to `B₀` is a covering map in the same convention. -/
theorem IsSurjectiveCoveringMap.restrictPreimage {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
    (hp : IsSurjectiveCoveringMap p) (B₀ : Set B) :
    IsSurjectiveCoveringMap (B₀.restrictPreimage p) :=
  (isSurjectiveCoveringMap_iff _).2
    ⟨hp.isCoveringMap.restrictPreimage B₀, B₀.restrictPreimage_surjective hp.surjective⟩

end
