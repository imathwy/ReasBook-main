module

import Topology_Munkres_2000.Book.Theorem_46_8
import Mathlib.Topology.UniformSpace.Ascoli

/- Remark 47.1: The general Arzelà–Ascoli theorem concerns compact subsets of
continuous-map spaces with the topology of compact convergence. Its proof compares
the topology of pointwise convergence, `FunctionTopology.compact`, and
`FunctionTopology.uniform`; on continuous maps, compact convergence is the
compact-open topology. -/
#check ArzelaAscoli.isCompact_of_equicontinuous
#check Pi.topologicalSpace
#check FunctionTopology.compact
#check FunctionTopology.uniform
#check ContinuousMap.compactOpen_eq_compactConvergence
