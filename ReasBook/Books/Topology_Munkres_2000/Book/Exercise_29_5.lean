module

public import Mathlib.Topology.Compactification.OnePoint.Basic

public section

/- Exercise 29.5: A homeomorphism `f : X₁ ≃ₜ X₂` of locally compact Hausdorff
spaces extends to a homeomorphism `OnePoint X₁ ≃ₜ OnePoint X₂` of their one-point
compactifications. The construction in fact requires no separation or local compactness
assumptions. -/
#check Homeomorph.onePointCongr
