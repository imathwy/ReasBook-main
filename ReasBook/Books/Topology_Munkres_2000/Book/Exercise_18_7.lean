module

public import Topology_Munkres_2000.Book.Exercise_18_7.Continuity

public section

/-- Exercise 18.7 (a). If `f : ℝ → ℝ` is continuous from the right at every
point, expressed by `ContinuousWithinAt f (Set.Ici a) a`, then it is continuous
from the Sorgenfrey line to the usual real line. -/
theorem continuous_sorgenfrey_of_continuousFromRight
    (f : ℝ → ℝ) (h_right : ∀ a : ℝ, ContinuousWithinAt f (Set.Ici a) a) :
    Continuous (f ∘ SorgenfreyLine.toReal) :=
  -- Apply the characterization of Sorgenfrey continuity by pointwise right-continuity.
  (SorgenfreyLine.continuous_comp_toReal_iff f).2 h_right

/- Part (b) asks for conjectures rather than asserting additional propositions. -/
