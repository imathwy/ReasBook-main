module

public import Topology_Munkres_2000.Book.Definition_54_2.LiftingCorrespondence

public section

/- Definition 54.2. For a covering map `p : E → B`, a base point `b₀ : B`, and a
chosen point `e₀ : p ⁻¹' {b₀}`, the lifting correspondence sends each element of
`FundamentalGroup B b₀` to the endpoint of its lift beginning at `e₀`. -/
#check IsCoveringMap.liftingCorrespondence
