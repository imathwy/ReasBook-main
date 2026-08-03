module

import Mathlib.Topology.Covering.Basic

/- Exercise 54.2. The rectangles are considered row by row so that the overlap
of each new rectangle with the region already treated is the connected union of
its left and bottom edges. The image of this overlap under the existing lift is
therefore connected, so it lies in one sheet of the covering. The inverse branch
for that sheet agrees with the existing lift on the whole overlap because both
are lifts there and agree at the common corner. With an arbitrary order, the
overlap can be disconnected, and its components could lie in different sheets. -/
#check IsCoveringMap.eqOn_of_comp_eqOn
#check IsPreconnected.image
