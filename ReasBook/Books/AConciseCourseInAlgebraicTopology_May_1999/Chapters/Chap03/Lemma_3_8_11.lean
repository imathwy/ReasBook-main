import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Theorem_3_8_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped FundamentalGroup
universe u

namespace IsUniversalCoveringMap

variable {E B : Type u} [TopologicalSpace E] [LocPathConnectedSpace E] [TopologicalSpace B]
  {p : C(E, B)}

/-- Lemma 3.8.11: for the quotient covering `E / H → B` attached to a subgroup
`H ≤ π₁(B, p e)` of a universal cover, the subgroup associated to the canonical orbit class of
`e` is exactly `H`. -/
-- Proof sketch: identify the associated subgroup with the monodromy stabilizer of the canonical
-- orbit point in the fiber over `p e`, then compare that stabilizer with the stabilizer of the
-- identity coset in `π₁(B, p e) / H` via the restriction of the quotient map `E → E / H`.
theorem universalCoverOrbitProjection_associatedSubgroup_eq
    [hp : IsUniversalCoveringMap p] (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) :
    (FundamentalGroup.map
      (universalCoverOrbitProjection e H) (universalCoverOrbitPoint e H)).range = H := by
  have hmap :
      FundamentalGroup.map (universalCoverOrbitProjection e H) (universalCoverOrbitPoint e H) =
        FundamentalGroup.mapOfEq (universalCoverOrbitProjection e H) rfl :=
    FundamentalGroup.map_eq_mapOfEq_rfl (universalCoverOrbitPoint e H)
  calc
    (FundamentalGroup.map
      (universalCoverOrbitProjection e H) (universalCoverOrbitPoint e H)).range =
        (FundamentalGroup.mapOfEq
          (universalCoverOrbitProjection e H)
          (universalCoverOrbitProjection_point e H)).range := by
            simpa [universalCoverOrbitProjection_point] using congrArg (fun f ↦ f.range) hmap
    _ = H := universalCoverOrbitProjection_range_eq_subgroup e H

end IsUniversalCoveringMap
