import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (G : Type u) [Group G]

/- Definition 8-8.3-3: the canonical owner for the notion of a nilpotent group is
`Group.IsNilpotent G`. -/
recall Group.IsNilpotent

/- The source-facing finite central-series formulation is derived API: it is exactly the canonical
bridge theorem `nilpotent_iff_finite_ascending_central_series`, not a second owner declaration. -/
recall nilpotent_iff_finite_ascending_central_series

end
