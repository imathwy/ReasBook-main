module

import Topology_Munkres_2000.Book.Definition_69_6.Relations

/- Definition 69.6. For a generator map `a : J → G`, the relations subgroup is
the kernel of `FreeGroup.lift a`. A family `r : β → FreeGroup J` is complete when
`Set.range r` normally generates this kernel. The canonical presented group has
this property for its defining relators. -/
#check FreeGroup.Relations.subgroup
#check FreeGroup.Relations.NormallyGeneratesKernel
#check FreeGroup.Relations.subset_ker
#check PresentedGroup.normallyGeneratesKernel
