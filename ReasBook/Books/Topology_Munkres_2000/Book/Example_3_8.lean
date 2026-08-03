module

public import Topology_Munkres_2000.Book.Example_3_2
public import Mathlib.Order.Defs.Unbundled

public section

namespace Kinship

/- Example 3.8 returns to the relations from Example 3.1. The relevant facts
already established here are that the blood relation is not transitive and the
sibling relation is an equivalence relation; `IsStrictOrder` is the canonical
notion used for the descendant relation's remaining order properties. -/
#check blood_not_transitive
#check sibling.instIsEquiv
#check IsStrictOrder

end Kinship
