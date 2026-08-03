module

import Mathlib.Topology.Basic

/- Definition 17.2: A topology may equivalently be specified by a collection of
closed sets containing `∅`, closed under arbitrary intersections and finite
unions, with open sets defined as their complements. -/
#check TopologicalSpace.ofClosed
