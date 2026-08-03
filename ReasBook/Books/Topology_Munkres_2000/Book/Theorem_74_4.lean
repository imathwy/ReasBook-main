module

public import Topology_Munkres_2000.Book.Definition_74_6.Presentation
public import Topology_Munkres_2000.Book.Theorem_74_4.Presentation
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

public section

namespace NonorientableSurfacePresentation

/-- Theorem 74.4. For `1 < m`, the fundamental group of the `m`-fold projective plane is
multiplicatively equivalent to the group on generators indexed by `Fin m` with ordered relator
`α₀² * ⋯ * αₘ₋₁²`. -/
theorem fundamentalGroupMulEquiv (m : ℕ) (hm : 1 < m) (x₀ : mFoldProjectivePlane m hm) :
    Nonempty
      (FundamentalGroup (mFoldProjectivePlane m hm) x₀ ≃*
        NonorientableSurfaceGroup.Presentation m) := sorry

end NonorientableSurfacePresentation
