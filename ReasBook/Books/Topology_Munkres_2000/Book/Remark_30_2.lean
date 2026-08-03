module

import Topology_Munkres_2000.Book.Exercise_4_99_2
import Mathlib.Topology.Bases

/- Remark 30.2 (1). The second countability axiom implies the first countability
axiom. -/
#check TopologicalSpace.SecondCountableTopology.to_firstCountableTopology

/- A topological basis restricts to a neighborhood basis consisting of the basis
elements containing a given point. -/
#check TopologicalSpace.IsTopologicalBasis.nhds_hasBasis

/- Remark 30.2 (2). Not every metric space is second-countable. -/
#check not_every_metricSpace_secondCountable
