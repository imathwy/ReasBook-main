module

import Mathlib.Data.Set.Finite.Basic

/- Remark 9.1: Taking `γ` to be the subtype `A`, the displayed prescription is
modeled by specializing the relation to
`P c t := if t = ∅ then c = a₁ else c ∉ t`. Infinitude of `A` supplies a fresh
element for every nonempty finite history. This relational prescription does
not determine a unique sequence, and positive-integer indexing is obtained by
reindexing the resulting natural-number sequence. -/
#check Set.seq_of_forall_finite_exists
