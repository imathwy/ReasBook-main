module

public import Topology_Munkres_2000.Book.Exercise_71_1.CircleUnion

public section

universe u v

namespace Topology

/-- Definition 71.2: A finitely indexed family of circles covering a Hausdorff space and meeting
pairwise exactly at a specified point is a finite wedge of circles. -/
class IsFiniteWedgeOfCircles {ι : Type v} [Fintype ι]
    {X : Type u} [TopologicalSpace X] (S : ι → Set X) (p : X) : Prop
    extends IsCircleUnion S p where
  /-- The ambient space is Hausdorff. -/
  t2Space : T2Space X

end Topology

end
