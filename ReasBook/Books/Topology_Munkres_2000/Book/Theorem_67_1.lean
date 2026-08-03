module

public import Topology_Munkres_2000.Book.Definition_67_4.ExternalDirectSum

public section

/- Theorem 67.1. The finitely supported dependent functions `DirectSum ι G`, with canonical
coordinate inclusions `DirectSum.inclusion G α`, form an external direct sum of the abelian groups
`G α`. -/
#check DirectSum.instIsExternalDirectSum

/- The coordinate maps in the construction are injective. -/
#check DirectSum.inclusion_injective
