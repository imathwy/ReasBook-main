module

import Mathlib.Data.PNat.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.WellFounded

/- Remark 10.1: The positive integers `ℕ+` have a well-founded strict order, so every nonempty
subset has a minimal element. Since `ℕ+` is linearly ordered, `Minimal` is equivalent to
`IsLeast`, the textbook's “smallest element.” -/
#synth WellFoundedLT ℕ+

#check (WellFoundedLT.exists_minimal (inferInstance : WellFoundedLT ℕ+) :
  ∀ s : Set ℕ+, s.Nonempty → ∃ m, Minimal (· ∈ s) m)

#check (minimal_iff_isLeast :
  ∀ {s : Set ℕ+} {m : ℕ+}, Minimal (· ∈ s) m ↔ IsLeast s m)
