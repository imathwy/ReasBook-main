module

public import Mathlib.Topology.Constructions

public section

universe u

/- Exercise 22.2 (1): A continuous map with a continuous right inverse is a quotient map. -/
#check Topology.IsQuotientMap.of_inverse

namespace Topology.IsQuotientMap

/-- Exercise 22.2 (2): A continuous retraction onto a subset is a quotient map. -/
theorem of_retraction {X : Type u} [TopologicalSpace X] {A : Set X}
    (r : X → A) (h_continuous : Continuous r) (hr : Function.LeftInverse r Subtype.val) :
    IsQuotientMap r :=
  of_inverse continuous_subtype_val h_continuous hr

end Topology.IsQuotientMap

end
