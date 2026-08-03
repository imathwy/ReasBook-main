module

import Mathlib.SetTheory.Cardinal.Finite

/- Remark 6.2. A bijection with `Fin n` identifies `n` with the canonical finite
cardinality `Nat.card A`, so two correct finite counts cannot disagree. -/
#check Nat.card_eq_of_equiv_fin
