module

public import ComputationalMethodsInverseProblems_Vogel_2002.Book.Ch3.Definition_3_2

public section

universe u

variable {X : Type u} [AddCommGroup X] [Module ℝ X]
variable (J : X → ℝ) (f_v p_v : X) (τ : ℝ)

/- Notation 3.4-extra-1. For fixed `f_v, p_v ∈ ℝ^n`, the source notation
`φ(τ) = J (f_v + τ • p_v)` is the existing owner `LineSearch.profile J f_v p_v`.
The reformulated line-search problem `min_{τ > 0} φ(τ)` is the source-facing
predicate `LineSearch.IsExactStep J f_v p_v τ`, whose canonical minimizer
component is `IsMinOn (LineSearch.profile J f_v p_v) (Set.Ioi (0 : ℝ)) τ`.
-/

#check LineSearch.profile

#check LineSearch.IsExactStep J f_v p_v τ
#check IsMinOn (LineSearch.profile J f_v p_v) (Set.Ioi (0 : ℝ)) τ
