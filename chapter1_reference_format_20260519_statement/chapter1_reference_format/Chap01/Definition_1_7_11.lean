import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 1.7.11: a partial order relation on `S` is a binary relation `≤` satisfying
reflexivity, antisymmetry, and transitivity. The companion notion of total order is the canonical
relation-level predicate `IsLinearOrder`. -/
recall IsPartialOrder (S : Sort u) (le : S → S → Prop) : Prop

/- A total order relation on `S` is a partial order relation for which any two elements are
comparable; this is the canonical relation-level predicate `IsLinearOrder`. -/
recall IsLinearOrder (S : Sort u) (le : S → S → Prop) : Prop
