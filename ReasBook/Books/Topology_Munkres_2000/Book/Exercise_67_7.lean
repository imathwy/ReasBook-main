module

public import Topology_Munkres_2000.Book.Definition_67_4.ExternalDirectSum

public section

/- Exercise 67.7. Every indexed family of abelian groups has an external direct sum:
`DirectSum ι G`, together with the canonical inclusions `DirectSum.inclusion G`, is such a group. -/
#check DirectSum.instIsExternalDirectSum

/- Each canonical coordinate map is a monomorphism. -/
#check DirectSum.inclusion_injective
