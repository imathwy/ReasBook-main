import Archive.Examples.Kuratowski

/- Exercise 17.21 (1): Starting from any subset of a topological space, repeated
closure and complement operations produce at most fourteen distinct subsets. -/
#check Topology.ClosureCompl.ncard_isObtainable_le_fourteen

/- Exercise 17.21 (2): The explicit subset `Topology.ClosureCompl.fourteenSet`
of `ℝ` attains the maximum of fourteen obtainable subsets. -/
#check Topology.ClosureCompl.fourteenSet
#check Topology.ClosureCompl.ncard_isObtainable_fourteenSet
