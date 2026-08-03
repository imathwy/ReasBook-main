module

public import Topology_Munkres_2000.Book.Definition_74_5.OrientablePasting
public import Topology_Munkres_2000.Book.Theorem_74_3.Presentation
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

public section

namespace OrientableSurfacePresentation

/-- Theorem 74.3. For `0 < n`, the fundamental group of the `n`-fold torus is isomorphic
to the quotient of the free group on generators `αᵢ`, `βᵢ` by the relation
`⁅α₀, β₀⁆ * ⋯ * ⁅αₙ₋₁, βₙ₋₁⁆ = 1`. -/
theorem fundamentalGroupMulEquiv (n : ℕ) (hn : 0 < n) (x₀ : nFoldTorus n hn) :
    Nonempty
      (FundamentalGroup (nFoldTorus n hn) x₀ ≃*
        OrientableSurfaceGroup.Presentation n) := sorry

end OrientableSurfacePresentation
