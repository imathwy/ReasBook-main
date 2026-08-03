module

public import Topology_Munkres_2000.Book.Theorem_70_1.Pushout

/- Exercise 70.4: If `X = U ∪ V`, where `U` and `V` are open and `U ∩ V` is path
connected with basepoint `x₀`, then the square of fundamental groups induced by the four
inclusions is a pushout square of groups. -/
#check FundamentalGroup.isPushoutOfOpenUnion
