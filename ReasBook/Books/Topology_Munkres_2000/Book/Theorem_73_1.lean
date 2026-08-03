module

public import Topology_Munkres_2000.Book.Theorem_73_1.Presentation

/- Theorem 73.1. The fundamental group of the torus has a presentation with two
generators `α`, `β` and the single relation `α * β * α⁻¹ * β⁻¹ = 1`. -/
#check TorusFundamentalGroup.presentation
#check TorusFundamentalGroup.relation
#check TorusFundamentalGroup.mulEquivPresentedGroup
