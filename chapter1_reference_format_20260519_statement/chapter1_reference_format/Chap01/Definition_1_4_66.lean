import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {α : Type u}

/- Definition 1.4.66: a set `X` is countable when it satisfies the canonical predicate
`Set.Countable X`; for a nonempty set, this is equivalent to the existence of a surjective map
`ℕ → X`, and such a surjection is a list/enumeration of `X`. A set is uncountable when this
countability predicate fails. -/
recall Set.Countable (X : Set α) : Prop

/- For a nonempty set, the textbook formulation of countability is exactly the existence of a
surjective map from `ℕ` onto the subtype defined by the set. -/
recall Set.countable_iff_exists_surjective {X : Set α} (hX : X.Nonempty) :
  X.Countable ↔ ∃ f : ℕ → X, Function.Surjective f
