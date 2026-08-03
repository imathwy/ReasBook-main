module

public import Topology_Munkres_2000.Book.Example_38_4

public section

/- Exercise 38.1 (1): Verify the circle-compactification extension criterion from
Example 38.4. -/
#check circleCompactification_extendable_iff

/- Exercise 38.1 (2): Verify the closed-interval-compactification extension criterion
from Example 38.4. -/
#check closedIntervalCompactification_extendable_iff

/- Exercise 38.1 (3): Verify that endpoint limits suffice for extension to the
topologist's-sine-curve compactification, as stated in Example 38.4. -/
#check endpointLimits_extendable_toSineCurve

/- Exercise 38.1 (4): Verify the explicit oscillating extension from Example 38.4. -/
#check TopologistsSineCurve.oscillatingExtension_apply
