import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v

variable (V : Type v) [NormedAddCommGroup V]

/- Definition 1.4.56: for a normed vector space, the Banach-space condition is exactly the
canonical predicate `CompleteSpace V`. This canonical owner lives at the level of the underlying
normed additive group: it says that the metric induced by the norm on `V` is complete. -/
#check (CompleteSpace V)
