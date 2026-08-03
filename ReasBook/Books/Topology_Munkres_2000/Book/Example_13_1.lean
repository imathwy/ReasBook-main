module

public import Topology_Munkres_2000.Book.Example_13_1.CircularRegions

public section

/-
Example 13.1. Circular regions form a basis for the Euclidean topology on the
plane, and a set is open exactly when each of its points lies in a circular
region contained in the set.
-/
#check EuclideanPlane.circularRegions
#check EuclideanPlane.mem_circularRegions_iff_ball
#check EuclideanPlane.isTopologicalBasis_circularRegions
#check EuclideanPlane.isOpen_iff_circularRegion_subset
