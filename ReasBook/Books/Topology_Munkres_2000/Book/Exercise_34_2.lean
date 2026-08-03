module

public import Topology_Munkres_2000.Book.Example_30_3.Countability
public import Topology_Munkres_2000.Book.Exercise_30_6
public import Topology_Munkres_2000.Book.Exercise_32_7.Separation

public section

/- Exercise 34.2 (1): The Sorgenfrey line is completely normal. -/
#check SorgenfreyLine.instT5Space

/- Exercise 34.2 (2): The Sorgenfrey line satisfies the first countability axiom. -/
#check SorgenfreyLine.instFirstCountableTopology

/- Exercise 34.2 (3): The Sorgenfrey line satisfies the Lindelöf condition. -/
#check SorgenfreyLine.instLindelofSpace

/- Exercise 34.2 (4): The Sorgenfrey line has a countable dense subset. -/
#check SorgenfreyLine.instSeparableSpace

/- Exercise 34.2 (5): The Sorgenfrey line is not metrizable. -/
#check SorgenfreyLine.notMetrizable
