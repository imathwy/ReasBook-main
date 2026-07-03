import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_1 (from Chap05) -/
universe u

section

variable {X : Type u} [PseudoMetricSpace X]
variable {C : Set X} {x : ℕ → X}

/-- Definition 5.1: a sequence `x : ℕ → X` is Fejer monotone with respect to `C` if for every
`c ∈ C` the distances `dist (x n) c` do not increase from one step to the next. In a seminormed
additive group this is the textbook inequality `‖x n - c‖`. -/
def FejerMonotone (C : Set X) (x : ℕ → X) : Prop :=
  ∀ c ∈ C, ∀ n : ℕ, dist (x (n + 1)) c ≤ dist (x n) c

-- Proof sketch: unfold `FejerMonotone` and specialize the defining inequality at the chosen
-- point `c ∈ C` and index `n`.
/-- A Fejer-monotone sequence satisfies the defining one-step distance inequality at each point of
`C`. -/
theorem FejerMonotone.step (h : FejerMonotone C x) (c : X) (hc : c ∈ C) (n : ℕ) :
    dist (x (n + 1)) c ≤ dist (x n) c :=
  h c hc n

end
