module

import Topology_Munkres_2000.Book.Definition_46_1.PointwiseTopology
import Topology_Munkres_2000.Book.Remark_19_1

universe u v

variable (J : Type u) (Y : Type v) [TopologicalSpace Y] (α : J) (U : Set Y)

/- Notation 46.1: The pointwise topology on `J → Y` is the product topology.
For `α : J` and `U : Set Y`, its standard subbasic set `pointwiseSubbasicSet α U`
is the preimage `Function.eval α ⁻¹' U` of `U` under the coordinate projection. -/
#check pointwiseSubbasicSet_eq_preimage α U
#check TopologicalSpace.pi_eq_generateFrom_projections
