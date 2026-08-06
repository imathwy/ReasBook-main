import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- Definition 3.2.6: a covering map `p : E → B` is regular, relative to a chosen basepoint
`e : E`, if `p` is a covering in the sense of Definition 3.1.5 and the image subgroup
`p_*(π₁(E,e)) ≤ π₁(B, p e)` is normal. -/
structure IsRegularCoveringMap (p : E → B) (e : E) : Prop
    where
  /-- A regular covering map is a path-connected covering map in the sense of Definition 3.1.5. -/
  isPathConnectedCoveringMap : IsPathConnectedCoveringMap p
  /-- The image subgroup of the induced homomorphism on fundamental groups at `e` is normal in
  the fundamental group of the base at `p e`. -/
  normal_fundamentalGroup_map_range :
    ((FundamentalGroup.map
        ⟨p, isPathConnectedCoveringMap.isCoveringMap.continuous⟩
        e).range).Normal

namespace IsRegularCoveringMap

variable {p : E → B} {e : E}

/-- A regular covering map is, in particular, a covering map. -/
theorem isCoveringMap (hp : IsRegularCoveringMap p e) : IsCoveringMap p :=
  hp.isPathConnectedCoveringMap.isCoveringMap

/-- A regular covering map is surjective. -/
theorem surjective (hp : IsRegularCoveringMap p e) : Function.Surjective p :=
  hp.isPathConnectedCoveringMap.surjective

/-- A regular covering map is, in particular, a path-connected covering map. -/
instance (hp : IsRegularCoveringMap p e) : IsPathConnectedCoveringMap p :=
  hp.isPathConnectedCoveringMap

/-- In a regular covering map, the image subgroup `p_*(π₁(E, e))` is normal in `π₁(B, p e)`. -/
instance (hp : IsRegularCoveringMap p e) :
    ((FundamentalGroup.map ⟨p, hp.isCoveringMap.continuous⟩ e).range).Normal :=
  hp.normal_fundamentalGroup_map_range

end IsRegularCoveringMap

namespace IsRegularCoveringMap

variable {p : C(E, B)} {e : E}

/-- In a regular covering map, the image subgroup `p_*(π₁(E, e))` is normal in `π₁(B, p e)`
when `p` is viewed as a continuous map. -/
instance (hp : IsRegularCoveringMap p e) :
    (FundamentalGroup.map p e).range.Normal := by
  simpa using hp.normal_fundamentalGroup_map_range

end IsRegularCoveringMap
