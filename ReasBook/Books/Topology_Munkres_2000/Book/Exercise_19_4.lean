module

public import Topology_Munkres_2000.Book.Exercise_19_4.FiniteProduct

/- Exercise 19.4: Indexing the factors by `Fin (n + 1)`, the product of the first
`n` spaces with the final space is homeomorphic to the full finite product. -/
#check Fin.snocHomeomorph
