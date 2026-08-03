module

public import Topology_Munkres_2000.Book.Definition_39_4.Refinement

public section

/- Definition 39.4 (1): A collection `ℬ` of subsets of `X` refines a collection
`𝒜` if every member of `ℬ` is contained in some member of `𝒜`. -/
#check IsRefinement

/- Definition 39.4 (2): An open refinement is a refinement whose members are
open sets. -/
#check IsOpenRefinement

/- Definition 39.4 (3): A closed refinement is a refinement whose members are
closed sets. -/
#check IsClosedRefinement
