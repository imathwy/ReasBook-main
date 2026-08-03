module

public import Mathlib.Combinatorics.SimpleGraph.Basic

public section

/- Example 64.2: The utilities graph is `completeBipartiteGraph (Fin 3) (Fin 3)`:
the left summand represents the three houses, the right summand represents the three
utilities, and every house is joined to every utility. Its non-embedding in `ℝ × ℝ`
is deferred to Theorem 64.2. -/
#check (completeBipartiteGraph (Fin 3) (Fin 3))
