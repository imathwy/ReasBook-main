module

public import Topology_Munkres_2000.Book.Definition_46_8.Currying
public import Mathlib.Topology.CompactOpen

public section

universe u v w

namespace ContinuousMap

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Theorem 46.11 (1). A continuous map `X × Z → Y` induces a continuous map
`Z → C(X, Y)` when `C(X, Y)` has the compact-open topology. -/
theorem continuous_of_continuous_uncurryRight (F : Z → C(X, Y))
    (hF : Continuous (uncurryRight F)) : Continuous F := by
  apply continuous_of_continuous_uncurry F
  exact (hF.comp continuous_swap).congr fun p ↦ by
    rcases p with ⟨z, x⟩
    change uncurryRight F (x, z) = F z x
    exact uncurryRight_apply F x z

/-- Theorem 46.11 (2). Under mathlib's locally compact hypothesis, uncurrying a continuous map
`Z → C(X, Y)` in the source's product order gives a continuous map `X × Z → Y`.
This slightly sharpens the source's locally compact Hausdorff assumption. -/
theorem continuous_uncurryRight_of_continuous [LocallyCompactSpace X]
    (F : Z → C(X, Y)) (hF : Continuous F) : Continuous (uncurryRight F) := by
  exact ((continuous_uncurry_of_continuous ⟨F, hF⟩).comp continuous_swap).congr fun p ↦ by
      rcases p with ⟨x, z⟩
      change F z x = uncurryRight F (x, z)
      exact (uncurryRight_apply F x z).symm

/-- Theorem 46.11, combined form. Under mathlib's locally compact hypothesis, a family
`F : Z → C(X, Y)` is continuous exactly when its evaluation on `X × Z` is continuous. -/
theorem continuous_uncurryRight_iff [LocallyCompactSpace X]
    (F : Z → C(X, Y)) : Continuous (uncurryRight F) ↔ Continuous F :=
  ⟨continuous_of_continuous_uncurryRight F, continuous_uncurryRight_of_continuous F⟩

end ContinuousMap
