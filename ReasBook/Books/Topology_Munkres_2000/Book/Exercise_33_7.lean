module

public import Topology_Munkres_2000.Book.Exercise_8_99_7.Separation

public section

universe u

/- Exercise 33.7: Every locally compact Hausdorff space is completely regular.
Here `T35Space` expresses the book's convention for a completely regular space. -/
#check fun (X : Type u) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] ↦
  ((LocallyCompactSpace.t2Space_iff_t35Space).mp inferInstance : T35Space X)
