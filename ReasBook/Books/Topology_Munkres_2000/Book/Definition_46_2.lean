module

public import Topology_Munkres_2000.Book.Proposition_46_1

public section

open scoped UniformConvergence

universe u v

variable (X : Type u) (Y : Type v) [TopologicalSpace X] [UniformSpace Y]

/- Definition 46.2: The topology of compact convergence announced here is the
topology of uniform convergence on the compact subsets of `X`. Its explicit basis
is given in Definition 46.3. -/
#check X →ᵤ[{K : Set X | IsCompact K}] Y
