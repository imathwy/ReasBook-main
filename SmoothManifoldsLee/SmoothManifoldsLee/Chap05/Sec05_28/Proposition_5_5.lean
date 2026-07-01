import Mathlib
import SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {M : Type u} [TopologicalSpace M] [T1Space M]

/- Proposition 5.5 is a source-facing specialization of the owner theorem
`Set.isProperlyEmbedded_iff_isClosed`: proper embedding here is the topological properness of the
subtype inclusion, so the embedded-submanifold hypotheses are derived context rather than
primitive data for the statement itself. -/
#check Set.isProperlyEmbedded_iff_isClosed

end
