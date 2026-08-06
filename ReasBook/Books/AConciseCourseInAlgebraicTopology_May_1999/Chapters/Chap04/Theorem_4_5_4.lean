import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Definition_2_4_1
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

universe u

open BasedSpace

-- `FundamentalGroup` is the canonical owner for `π₁`, and `BasedSpace` is the repository owner
-- for a space equipped with a chosen basepoint.

section

variable (G : Type u) [Group G]

namespace BasedSpace

/-- A based-space formulation of Theorem 4.5.4. -/
theorem exists_connected_fundamentalGroup_mulEquiv :
    ∃ X : BasedSpace.{u},
      ConnectedSpace X.right ∧
        Nonempty (FundamentalGroup X.right (underTopBasepoint X) ≃* G) := sorry

end BasedSpace

/-- Theorem 4.5.4: for any group `G`, there is a connected space `X` with a basepoint `x : X`
such that `π₁(X, x)` is isomorphic to `G`. -/
theorem exists_connectedSpace_fundamentalGroup_mulEquiv :
    ∃ (X : TopCat.{u}) (x : X), ConnectedSpace X ∧ Nonempty (FundamentalGroup X x ≃* G) := by
  rcases BasedSpace.exists_connected_fundamentalGroup_mulEquiv G with ⟨X, hX, hπ₁⟩
  exact ⟨X.right, underTopBasepoint X, hX, hπ₁⟩

end
