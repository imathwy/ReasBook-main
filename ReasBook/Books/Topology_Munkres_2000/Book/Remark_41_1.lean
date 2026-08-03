module

public import Topology_Munkres_2000.Book.Theorem_41_4.Paracompact

public section

/- Remark 41.1 (1). Every compact space is paracompact. -/
#check paracompact_of_compact

/- Remark 41.1 (2). Every metrizable space is paracompact. -/
#check TopologicalSpace.MetrizableSpace.paracompactSpace
