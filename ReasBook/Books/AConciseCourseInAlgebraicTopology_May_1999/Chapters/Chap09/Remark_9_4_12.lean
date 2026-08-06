import Mathlib.GroupTheory.OrderOfElement
import Books.AConciseCourseInAlgebraicTopology_May_1999.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Sphere

noncomputable section

open scoped TopCat Topology Topology.Homotopy

-- Semantic recall via `lean_leansearch`: `HomotopyGroup.Pi`, written `π_ n X x`, is the
-- canonical owner for based homotopy groups. Chapter 9 already fixes the standard sphere
-- basepoint as `sphereBasepoint`, so this remark reuses that owner directly.

/-- Remark 9.4.12 (1): the quaternionic Hopf bundle `S^7 → S^4` yields an element of infinite
order in `π_ 7 (𝕊 4)` at the standard sphere basepoint `sphereBasepoint 4`. -/
theorem pi7SphereFour_hasInfiniteOrderElement :
    ∃ x : π_ 7 (𝕊 4) (sphereBasepoint 4), orderOf x = 0 := sorry

/-- Remark 9.4.12 (2): the Cayley Hopf bundle `S^15 → S^8` yields an element of infinite order in
`π_ 15 (𝕊 8)` at the standard sphere basepoint `sphereBasepoint 8`. -/
theorem pi15SphereEight_hasInfiniteOrderElement :
    ∃ x : π_ 15 (𝕊 8) (sphereBasepoint 8), orderOf x = 0 := sorry
