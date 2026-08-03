module

public import Mathlib.Topology.Connected.LocallyConnected

/- Definition 25.3: A space is locally connected when every neighborhood of each point
contains an open connected neighborhood of that point. -/
#check LocallyConnectedSpace
#check locallyConnectedSpace_iff_subsets_isOpen_isConnected
