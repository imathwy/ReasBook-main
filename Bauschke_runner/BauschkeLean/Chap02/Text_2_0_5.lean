import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Text 2.0.5: a family in a real Hilbert space is summable exactly when its finite partial sums
converge to some limit in the canonical mathlib sense; this is the definition of `Summable` via
the existence of a `HasSum` limit along the unconditional summation filter. -/
recall Summable

/- For a family of extended nonnegative reals, the infinite sum is the supremum of the sums over
finite subsets. -/
recall ENNReal.tsum_eq_iSup_sum {α : Type u} {f : α → ENNReal} :
    ∑' (a : α), f a = ⨆ s, ∑ a ∈ s, f a
