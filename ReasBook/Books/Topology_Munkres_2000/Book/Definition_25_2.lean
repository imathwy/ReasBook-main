module

public import Topology_Munkres_2000.Book.Definition_24_3.PathConnectedness

/- Definition 25.2: `pathSetoid X` is the equivalence relation on `X` given by
`Joined`, and `pathComponent x` is the equivalence class containing `x`. -/
#check pathSetoid
#check pathComponent

/- Membership in the path component of `x` means being joined to `x` by a path. -/
#check mem_pathComponent_iff
