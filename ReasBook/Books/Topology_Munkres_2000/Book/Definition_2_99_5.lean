module

public import Topology_Munkres_2000.Book.Definition_2_99_5.SymmetricSet

public section

universe u

/- Definition 2.99.5: A neighborhood `V` of the identity element is symmetric when
`V.IsSymmetric`, meaning `V = V⁻¹`. The predicate itself depends only on the group
structure and applies to any subset. -/
#check fun {G : Type u} [Group G] (V : Set G) ↦ (V.IsSymmetric : Prop)
