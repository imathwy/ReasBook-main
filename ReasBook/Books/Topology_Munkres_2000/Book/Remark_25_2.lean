module

public import Topology_Munkres_2000.Book.Definition_25_2

public section

/- Remark 25.2: After parametrizing paths by `unitInterval`, path-joinability is
reflexive, symmetric, and transitive. The three laws are witnessed respectively
by constant paths, reversed paths, and concatenated paths, and are packaged by
`pathSetoid`. -/
#check Joined.refl
#check Joined.symm
#check Joined.trans
#check pathSetoid
