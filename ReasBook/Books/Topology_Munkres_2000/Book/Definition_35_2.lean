module

public import Topology_Munkres_2000.Book.Definition_35_2.Extension

public section

/-
Definition 35.2. A topological space `Y` has the universal extension property
when every continuous map `f : C(A, Y)` from a closed subset `A` of a normal
space `X` extends to a continuous map on `X`.
-/
#check UniversalExtensionProperty
#check UniversalExtensionProperty.exists_restrict_eq
#check TietzeExtension.universalExtensionProperty
