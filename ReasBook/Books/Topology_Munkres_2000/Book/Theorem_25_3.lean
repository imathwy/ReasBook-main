module

public import Mathlib.Topology.Connected.LocallyConnected

/- Theorem 25.3: A space `X` is locally connected if and only if, for every open set
`U` in `X`, each connected component of `U` is open in `X`. -/
#check locallyConnectedSpace_iff_connectedComponentIn_open
