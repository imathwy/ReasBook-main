module

import Topology_Munkres_2000.Book.Theorem_42_1
import Topology_Munkres_2000.Book.Exercise_34_7
import Topology_Munkres_2000.Book.Exercise_34_8
import Topology_Munkres_2000.Book.Theorem_41_5.Paracompact

/- Exercise 42.1: Compare Theorem 42.1 with Exercises 7 and 8 of §34.
Exercise 34.7 follows from Smirnov's theorem because compact spaces are paracompact.
Exercise 34.8 follows because regular Lindelöf spaces are paracompact; its `T3Space`
assumption also supplies the Hausdorff hypothesis. -/
#check TopologicalSpace.metrizableSpace_iff_paracompact_t2_locallyMetrizable
#check LocallyMetrizableSpace.metrizableSpace_of_paracompact_t2
#check LocallyMetrizableSpace.metrizableSpace_of_compact
#check LocallyMetrizableSpace.metrizableSpace_of_t3_lindelof
#check paracompact_of_compact
#check paracompact_of_t3_lindelof
