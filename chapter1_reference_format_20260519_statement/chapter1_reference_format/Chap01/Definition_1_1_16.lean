import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 1.1.16 (1): a strict partial order on a set `S` is a binary relation `<` on `S`
that is irreflexive and transitive; the textbook's asymmetry clause is part of this standard
strict-order package. -/
recall IsStrictOrder (S : Type u) (lt : S → S → Prop) : Prop

/- Definition 1.1.16 (2): a strict total order on a set `S` is a strict partial order whose
distinct elements are always comparable by `<`; this is the standard strict-total-order notion. -/
recall IsStrictTotalOrder (S : Type u) (lt : S → S → Prop) : Prop
