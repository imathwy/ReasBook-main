module

public import Topology_Munkres_2000.Book.Theorem_54_6.Monodromy
import all Topology_Munkres_2000.Book.Theorem_54_6.Monodromy

public section

universe u v

/- Notation 13.0.1: For a covering map `p : E → B` with `p e₀ = b₀`, the subgroup
`H₀` is `hp.fundamentalGroupMapRange he₀`; the induced homomorphism is injective, and
`π₁(E, e₀)` is canonically isomorphic to this range subgroup. -/
#check IsCoveringMap.fundamentalGroupMapRange
#check IsCoveringMap.fundamentalGroupMap_injective

#check fun {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (hp : IsCoveringMap p) {e₀ : E} {b₀ : B} (he₀ : p e₀ = b₀) ↦
  (MonoidHom.ofInjective (hp.fundamentalGroupMap_injective he₀) :
    FundamentalGroup E e₀ ≃* hp.fundamentalGroupMapRange he₀)
