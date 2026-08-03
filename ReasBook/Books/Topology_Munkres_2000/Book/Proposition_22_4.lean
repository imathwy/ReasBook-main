module

import Mathlib.Topology.Constructions.SumProd

/- Proposition 22.4: If quotient maps `p` and `q` are open maps, then their
coordinatewise product, denoted in the source by `p × q` and represented by
`Prod.map p q`, is open and hence is a quotient map. The predicate
`IsOpenQuotientMap` is equivalent to being both open and a quotient map. -/
#check IsOpenQuotientMap.prodMap
#check IsOpenQuotientMap.iff_isOpenMap_isQuotientMap
