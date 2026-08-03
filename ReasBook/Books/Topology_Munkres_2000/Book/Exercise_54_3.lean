module

public import Topology_Munkres_2000.Book.Exercise_54_3.Concatenation

public section

/- Exercise 54.3. Concatenating liftings with matching endpoints gives a lifting of
the concatenated paths. The covering-map assumption is not needed for this fact. -/
#check ContinuousMap.IsLift.transPath
