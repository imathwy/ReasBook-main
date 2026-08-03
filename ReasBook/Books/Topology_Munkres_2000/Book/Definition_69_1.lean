module

public import Topology_Munkres_2000.Book.Definition_69_1.Generators

/- Definition 69.1. A family `a : J → G` generates a group `G` when
`Group.Generates a`. A group is finitely generated when it has a finite
generating family, equivalently when `Group.FG G` holds. -/
#check Group.Generates
#check Group.generates_iff
#check Group.generates_iff_lift_surjective
#check Group.Generates.fg
#check Group.FG
#check Group.fg_iff
