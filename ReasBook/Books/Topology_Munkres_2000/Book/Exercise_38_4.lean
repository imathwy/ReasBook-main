module

public import Topology_Munkres_2000.Book.Exercise_38_4.Comparison

public section

universe u v

namespace Compactification

/-- Exercise 38.4. Every compactification is the image of the Stone–Čech compactification under
a continuous surjective closed map that is the identity on the original space. -/
theorem stoneCechComparison_spec {X : Type u} [TopologicalSpace X] [T35Space X]
    (C : Compactification.{u, v} X) :
    Function.Surjective (stoneCechComparison C) ∧
      IsClosedMap (stoneCechComparison C) ∧
      ∀ x : X, stoneCechComparison C (stoneCech X x) = C x := by
  exact ⟨stoneCechComparison_surjective C, stoneCechComparison_isClosedMap C,
    stoneCechComparison_apply C⟩

end Compactification
