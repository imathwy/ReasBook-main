module

public import Topology_Munkres_2000.Book.Definition_52_6.BasepointChange

/- Definition 52.6. A path `α : Path x₀ x₁` induces the basepoint-change map
`α̂ : π₁(X, x₀) → π₁(X, x₁)`, sending the class of a loop `f` to the class represented by
`α.symm.trans (f.trans α)`. -/
#check FundamentalGroup.LeftToRight.hat
#check FundamentalGroup.LeftToRight.toPath_hat_apply
