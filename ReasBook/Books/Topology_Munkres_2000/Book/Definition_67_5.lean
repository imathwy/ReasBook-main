module

public import Topology_Munkres_2000.Book.Definition_67_5.Basis

public section

universe u v

variable {G : Type u} [AddCommGroup G] {ι : Type v}
variable (a : ι → G)

/- Definition 67.5 (1). The indexed elements `a` generate `G` when their integer span is
all of `G`. -/
#check Submodule.span ℤ (Set.range a) = (⊤ : Submodule ℤ G)

/- Definition 67.5 (2). The abelian group `G` is free with the specified indexed family
`a` as a basis exactly when `Module.IsBasis ℤ a` holds. -/
#check Module.IsBasis ℤ a
