module

import Topology_Munkres_2000.Book.Theorem_3_0_1
import Topology_Munkres_2000.Book.Theorem_3_0_2
import Topology_Munkres_2000.Book.Theorem_3_0_3

/- Remark 3.0.2. The intermediate value theorem reflects connectedness of the closed
interval `Set.Icc a b`, while the maximum value and uniform continuity theorems reflect
its compactness, in addition to the continuity of the function. -/
#check intermediateValueOnIcc
#check isConnected_Icc
#check isPreconnected_Icc
#check IsPreconnected.intermediate_value

#check maximumValueOnIcc
#check isCompact_Icc
#check IsCompact.exists_isMaxOn

#check uniformContinuityOnIcc
#check CompactSpace.uniformContinuous_of_continuous
