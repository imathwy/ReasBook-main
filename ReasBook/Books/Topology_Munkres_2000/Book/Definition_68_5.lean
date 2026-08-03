module

public import Topology_Munkres_2000.Book.Definition_68_5.ExternalFreeProduct

public section

/- Definition 68.5: An ambient group is the external free product of an indexed family
relative to specified monomorphisms when their images form an internal free-product
decomposition. -/
#check MonoidHom.IsExternalFreeProduct

namespace Monoid.CoprodI

universe u v

variable {ι : Type u} (G : ι → Type v) [∀ α, Group (G α)]

/-- Definition 68.5: The canonical inclusions exhibit `Monoid.CoprodI G` as the external free
product of the indexed family `G`. -/
instance instIsExternalFreeProduct :
    MonoidHom.IsExternalFreeProduct (fun α ↦ (of : G α →* Monoid.CoprodI G)) :=
  canonicalIsExternalFreeProduct G

end Monoid.CoprodI
