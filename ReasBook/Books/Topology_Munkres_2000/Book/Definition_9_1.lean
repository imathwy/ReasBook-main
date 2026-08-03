module

public import Topology_Munkres_2000.Book.Definition_9_1.ChoiceFunction

public section

/- Definition 9.1: A function `c : 𝓑 → ⋃₀ 𝓑` satisfying `c B ∈ B` for every
`B : 𝓑` is called a choice function for the collection `𝓑`. -/
#check Set.IsChoiceFunction
#check Set.IsChoiceFunction.mem
