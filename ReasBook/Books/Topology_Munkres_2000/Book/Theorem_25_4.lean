module

public import Mathlib.Topology.Connected.LocallyPathConnected

/- Theorem 25.4: A space `X` is locally path connected if and only if, for every open
set `U` in `X`, each path component of `U` is open in `X`. -/
#check locallyPathConnectedSpace_iff_isOpen_pathComponentIn
