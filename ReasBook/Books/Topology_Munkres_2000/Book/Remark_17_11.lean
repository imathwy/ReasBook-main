module

import Mathlib.Topology.Bases
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Separation.Hausdorff

/- Remark 17.11: The Hausdorff and `T₁` conditions are separation axioms;
other standard families of topological conditions include countability axioms,
compactness conditions, and connectedness conditions. These conditions are studied
in the following chapters, and some impose quite stringent requirements. -/
#check T1Space
#check T2Space
#check T2Space.t1Space
#check FirstCountableTopology
#check SecondCountableTopology
#check CompactSpace
#check ConnectedSpace
