import Mathlib.Probability.Martingale.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 12.11 is `source-facing`: it names a backward martingale. Its `core/canonical`
owner is exactly `MeasureTheory.Martingale`. The only `bridge/view` content is the textbook
reverse-time index set `-ℕ₀`, formalized in Lean by `OrderDual ℕ`. Thus the primitive data are
just a process on `OrderDual ℕ`, a filtration on `OrderDual ℕ`, and a measure; there is no
separate backward-martingale wrapper API to keep alongside the owner predicate.
-/
recall MeasureTheory.Martingale
