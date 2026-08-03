module

public import Topology_Munkres_2000.Book.Example_12_1.ThreePointTopology

public section

open ThreePointTopology
open scoped Topology

/- Example 12.1: The labeled set `{a, b, c}` admits the displayed topology with
open sets `∅`, `{b}`, `{a, b}`, `{b, c}`, and `Set.univ`, as well as the
indiscrete, discrete, and relabeled displayed topologies. -/
#check ThreePointTopology.ThreePoint
#check ThreePointTopology.topology .bAndABAndBC
#check ThreePointTopology.openSets .bAndABAndBC
#check ThreePointTopology.isOpen_iff .bAndABAndBC
#check IsClosed[topology .bAndABAndBC]
#check ThreePointTopology.Displayed.neighborhoods .bAndABAndBC
#check ThreePointTopology.topology .indiscrete
#check ThreePointTopology.topology_indiscrete
#check ThreePointTopology.topology .discrete
#check ThreePointTopology.topology_discrete
