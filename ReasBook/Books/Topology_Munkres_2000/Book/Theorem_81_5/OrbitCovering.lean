module

public import Topology_Munkres_2000.Book.Definition_81_5.HomeomorphGroup
public import Topology_Munkres_2000.Book.Proposition_81_2.Covering

public section

open scoped HomeomorphGroup

universe u

namespace HomeomorphGroup

/-- The connected covering determined by an orbit projection that is a covering map. -/
@[expose]
def covering {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    [LocallyPathConnectedSpace X] (G : Subgroup (X ≃ₜ X))
    (hp : IsCoveringMap (mk G)) : ConnectedCovering (X / G) :=
  ConnectedCovering.of (mk G) hp Quotient.mk''_surjective

end HomeomorphGroup
