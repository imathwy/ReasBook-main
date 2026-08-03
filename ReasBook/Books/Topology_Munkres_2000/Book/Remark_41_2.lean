module

import Mathlib.Topology.PartitionOfUnity

/- Remark 41.2: a partition of unity subordinate to an open family patches
functions continuous on the corresponding open sets into the global function
`fun x ↦ ∑ᶠ i, f i x • g i x`, which is continuous. -/
#check PartitionOfUnity.IsSubordinate.continuous_finsum_smul
