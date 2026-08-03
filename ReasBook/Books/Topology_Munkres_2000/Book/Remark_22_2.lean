module

import Mathlib.Topology.Maps.Basic

/- Remark 22.2 (1): The quotient-map condition is stronger than continuity:
every quotient map is continuous. -/
#check Topology.IsQuotientMap.continuous

/- Remark 22.2 (2): Equivalently, a quotient map is characterized by
surjectivity and preservation and reflection of closedness under preimage. -/
#check Topology.isQuotientMap_iff_isClosed

-- Preimages commute with complements, relating the open- and closed-set forms.
#check Set.preimage_compl
