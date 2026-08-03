module

import Mathlib.Topology.Homotopy.Contractible

/- Definition 51.10: A topological space `X` is contractible exactly when
`ContinuousMap.id X` is nullhomotopic. -/
#check ContractibleSpace
#check contractible_iff_id_nullhomotopic
