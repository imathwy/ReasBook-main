module

import Mathlib.Logic.Basic

/- Proposition 1.2. For a set `A` and a predicate `P` on its elements,
`(¬ ∀ x ∈ A, P x) ↔ ∃ x ∈ A, ¬ P x`. -/
#check not_forall₂
