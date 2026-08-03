module

import Topology_Munkres_2000.Book.Exercise_1_99_1
import Mathlib.Data.PNat.Basic

public section

universe u

/- Exercise 8.8: A rule assigning an element of `A` to every `A`-valued
function on a section `Set.Iio n` of the positive integers determines a unique
function `h : ℕ+ → A` satisfying the corresponding recursive equation. -/
#check fun (A : Type u) (ρ : {n : ℕ+} → (Set.Iio n → A) → A) ↦
  (existsUniqueRecursiveDefinition ρ :
    ∃! h : ℕ+ → A, ∀ n : ℕ+, h n = ρ ((Set.Iio n).restrict h))
