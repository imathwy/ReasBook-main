module

public import Topology_Munkres_2000.Book.Example_30_3.Countability
public import Topology_Munkres_2000.Book.Example_31_2.Instances
public import Topology_Munkres_2000.Book.Theorem_41_5.Paracompact

public section

namespace SorgenfreyLine

/-- The Sorgenfrey line is paracompact. -/
instance instParacompactSpace : ParacompactSpace SorgenfreyLine :=
  paracompact_of_t3_lindelof

end SorgenfreyLine
