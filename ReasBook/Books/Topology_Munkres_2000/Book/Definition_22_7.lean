module

public import Topology_Munkres_2000.Book.Definition_22_6

public section

universe u

variable (X : Type u) [TopologicalSpace X] (P : Setoid.Partitions X)

/- Definition 22.7: A partition `P : Setoid.Partitions X` determines the equivalence relation
`(Setoid.Partition.orderIso X).symm P`, whose equivalence classes are exactly the blocks of `P`.
With the quotient topology from Definition 22.6, the block type `P.toSet` is also called an
identification space or decomposition space of `X`. -/
#check (Setoid.Partition.orderIso X).symm P
#check Setoid.classes_mkClasses P.toSet P.isPartition
#check P.quotientTopology

end
