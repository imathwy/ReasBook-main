import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (K : Type u) [Field K]

/- Lemma 10.50.2: let `K` be a field and let `A ⊂ K` be a local subring. Then there exists a
valuation ring with fraction field `K` dominating `A`. The primary domain is valuation theory for
local subrings of a field. This file is a `bridge/view` recall of the core owner theorem
`LocalSubring.exists_le_valuationSubring`: the primitive data are `K` and `A : LocalSubring K`,
while the domination relation `A ≤ B.toLocalSubring` is derived from the owner abstractions
`LocalSubring K` and `ValuationSubring K`. -/
recall LocalSubring.exists_le_valuationSubring

end
