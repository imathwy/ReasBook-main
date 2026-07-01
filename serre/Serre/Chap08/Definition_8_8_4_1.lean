import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 8-8.4-1: a Sylow `p`-subgroup of `G` is the canonical mathlib structure
`Sylow p G`. -/
recall Sylow

/- For a finite group, a subgroup whose cardinality is the full `p`-power dividing `Nat.card G`
is a Sylow `p`-subgroup via the canonical constructor `Sylow.ofCard`. -/
recall Sylow.ofCard
