module

public import Topology_Munkres_2000.Book.Example_29_3.Instances
public import Topology_Munkres_2000.Book.Theorem_27_1

public section

universe u

/- Example 29.3: A linear order with the least upper bound property is weakly locally
compact in its order topology. -/
#check fun (X : Type u) [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
    [LeastUpperBoundProperty X] ↦ (inferInstance : WeaklyLocallyCompactSpace X)
