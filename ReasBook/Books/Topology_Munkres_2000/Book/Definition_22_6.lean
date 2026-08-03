module

public import Topology_Munkres_2000.Book.Definition_22_6.QuotientSpace

public section

/- Definition 22.6: For a partition `P` of a topological space `X`, the canonical map
`P.block : X → P.toSet` sends each point to its block. The coinduced topology
`P.quotientTopology` makes the block type a quotient space of `X`. -/
#check Setoid.Partitions.block
#check Setoid.Partitions.quotientTopology
#check Setoid.Partitions.isQuotientTopology

end
