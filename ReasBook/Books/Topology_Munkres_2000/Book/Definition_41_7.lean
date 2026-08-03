module

import Mathlib.Topology.PartitionOfUnity

/- Definition 41.7. For an indexed open covering `U : ι → Set X`, a partition of
unity on `X` dominated by `U` is canonically represented by
`ρ : PartitionOfUnity ι X Set.univ` together with `ρ.IsSubordinate U`.
The structure gives continuous nonnegative real-valued functions with locally
finite supports and pointwise sum one; subordination says
`tsupport (ρ i) ⊆ U i` for every `i`. Nonnegativity and the sum condition imply
`ρ i x ≤ 1`, so these functions take values in `[0, 1]`. -/
#check PartitionOfUnity
#check PartitionOfUnity.IsSubordinate
#check PartitionOfUnity.locallyFinite_tsupport
#check PartitionOfUnity.nonneg
#check PartitionOfUnity.le_one
#check PartitionOfUnity.sum_eq_one
