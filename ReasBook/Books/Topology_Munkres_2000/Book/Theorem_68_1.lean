module

public import Topology_Munkres_2000.Book.Definition_68_5

public section

universe u v

variable {ι : Type u} (G : ι → Type v) [∀ α, Group (G α)]

/- Theorem 68.1: The indexed coproduct is a canonical group containing copies of the
groups `G α` isomorphic to them, whose ranges form an internal free-product decomposition. -/
#check Monoid.CoprodI G
#check fun α ↦ (Monoid.CoprodI.of : G α →* Monoid.CoprodI G)
#check fun α ↦
  (MonoidHom.ofInjective (Monoid.CoprodI.of_injective α) :
    G α ≃* (Monoid.CoprodI.of : G α →* Monoid.CoprodI G).range)
#check Monoid.CoprodI.instIsExternalFreeProduct
