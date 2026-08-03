module

import Mathlib.Logic.Basic

/- Proposition 1.3. For a set `A` and a predicate `Q` on its elements, the
negation of `∃ x ∈ A, Q x` is `∀ x ∈ A, ¬ Q x`. -/
#check not_exists_mem
