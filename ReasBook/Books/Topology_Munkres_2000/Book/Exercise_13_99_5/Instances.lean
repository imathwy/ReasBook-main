module

public import Topology_Munkres_2000.Book.Example_71_1.Earring
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

public section

namespace InfiniteEarring

/-- The infinite earring is compact. -/
instance instCompactSpace : CompactSpace Space := sorry

/-- The fundamental group of the infinite earring at its common origin is uncountable. -/
instance instUncountableFundamentalGroup :
    Uncountable (FundamentalGroup Space origin) := sorry

end InfiniteEarring

