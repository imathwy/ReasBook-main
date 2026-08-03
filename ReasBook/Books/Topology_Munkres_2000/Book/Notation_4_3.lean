module

public import Topology_Munkres_2000.Book.Notation_4_2

public section

/- Notation 4.3: In the positive integers `ℕ+`, the standard numeral symbols
satisfy `2 = 1 + 1`, `3 = 2 + 1`, and the analogous recursive convention
thereafter. -/
#check (rfl : (2 : ℕ+) = 1 + 1)
#check (rfl : (3 : ℕ+) = 2 + 1)
