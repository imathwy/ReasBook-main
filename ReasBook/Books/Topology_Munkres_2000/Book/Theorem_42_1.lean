module

public import Topology_Munkres_2000.Book.Remark_6_0_4

public section

/- Theorem 42.1 (Smirnov metrization theorem). A space is metrizable if and only if
it is paracompact, Hausdorff, and locally metrizable. -/
#check TopologicalSpace.metrizableSpace_iff_paracompact_t2_locallyMetrizable

/- The reverse implication as a typeclass instance. -/
#check LocallyMetrizableSpace.metrizableSpace_of_paracompact_t2
