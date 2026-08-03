module

public import Topology_Munkres_2000.Book.Definition_33_2

/- Theorem 33.2 (1): Every subspace of a completely regular space is completely regular.
In Lean, a subspace is a subtype with the induced topology. -/
#check instT35SpaceSubtype

/- Theorem 33.2 (2): An arbitrary product of completely regular spaces is completely regular. -/
#check instT35SpaceForall
