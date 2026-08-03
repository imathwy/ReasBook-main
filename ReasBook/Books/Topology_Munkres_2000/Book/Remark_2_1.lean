module

import Mathlib.Topology.Algebra.InfiniteSum.Real

universe u v

/- Remark 2.1: For sets `A : Set α` and `B : Set β`, a function assigning to
each element of `A` an element of `B` has type `A → B`. When a real-valued
function is specified only by a formula, its domain is the set of real numbers
for which that formula makes sense. -/
#check (fun {α : Type u} {β : Type v} (A : Set α) (B : Set β) ↦ A → B)

-- A polynomial formula defines a function on all real numbers.
#check (fun x : ℝ ↦ 3 * x ^ 2 + 2)

-- The geometric series defines a real-valued function on its summability domain.
#check (fun x : {x : ℝ // Summable (fun k : ℕ ↦ x ^ (k + 1))} ↦
  ∑' k : ℕ, (x : ℝ) ^ (k + 1))
