module

public import Topology_Munkres_2000.Book.Example_41_4.Instances
public import Topology_Munkres_2000.Book.Example_31_3.Separation

public section

/- Example 41.4 (1): The Sorgenfrey line is paracompact because it is regular
and Lindelöf. -/
#check SorgenfreyLine.instParacompactSpace

/- Example 41.4 (2): The Sorgenfrey plane is not normal in the book's
`T4Space` convention. -/
#check SorgenfreyPlane.notT4

namespace SorgenfreyPlane

/-- Example 41.4 (3): The Sorgenfrey plane is not paracompact. -/
theorem notParacompact : ¬ ParacompactSpace (SorgenfreyLine × SorgenfreyLine) := by
  intro h
  exact notT4 T4Space.of_paracompactSpace_t2Space

end SorgenfreyPlane
