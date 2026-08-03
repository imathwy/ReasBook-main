module

public import Topology_Munkres_2000.Book.Notation_4_2.Sections

public section

/- Notation 4.2: For `n : ℕ+`, the section `S_{n}` is the set of positive
integers less than `n`. The notation `{1, …, n}` denotes the positive integers
between `1` and `n`, inclusive. -/
#check fun n : ℕ+ ↦ (S_{n} : Set ℕ+)
#check (Set.Iio_bot : (S_{(1 : ℕ+)} : Set ℕ+) = ∅)
#check fun n : ℕ+ ↦
  (Set.Iio_add_one_eq_Iic n : (S_{n + 1} : Set ℕ+) = {1,…,n})
