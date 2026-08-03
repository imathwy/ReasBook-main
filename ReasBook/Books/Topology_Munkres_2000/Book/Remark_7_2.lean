module

import Mathlib.Data.PNat.Basic

/- Remark 7.2: The textbook set `A` of positive integers for which a theorem
holds is represented by a predicate `p : ℕ+ → Prop`. Its base membership and
closure under successor are precisely the hypotheses of positive-integer
induction. -/
#check fun (p : ℕ+ → Prop) (h_one : p 1)
    (h_succ : ∀ n : ℕ+, p n → p (n + 1)) (n : ℕ+) ↦
  (PNat.recOn n h_one h_succ : p n)
