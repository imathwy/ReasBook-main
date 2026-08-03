module

public import Mathlib.Topology.Constructions

public section

/- Lemma 16.2: Let `Y` be a subspace of `X`. If `U` is open in `Y` and `Y` is
open in `X`, then the image of `U` under `Subtype.val : Y → X` is open in `X`. -/
#check IsOpen.isOpenMap_subtype_val
