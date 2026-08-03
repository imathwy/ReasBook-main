module

public import Topology_Munkres_2000.Book.Example_28_2.Instances

public section

/- Example 28.2 (1): The open first-uncountable ordinal is not compact. -/
#check (inferInstance : NoncompactSpace OpenOmegaOne)

/- Example 28.2 (2): The open first-uncountable ordinal is limit point compact. -/
#check (inferInstance : LimitPointCompactSpace OpenOmegaOne)
