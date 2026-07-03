import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_17_20 (from Chap17) -/
universe u

namespace ERealFunction

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- Definition 17.20: a vector `y` is a descent direction of a proper convex `]-∞,+∞]`-valued
function `f` at a point `x` of its effective domain when there is a positive radius `ε` such that
every step `x + α • y` with `α ∈ ]0, ε]` strictly decreases the value of `f`. -/
def IsDescentDirectionAt (f : H → Set.Ioi (⊥ : EReal)) (x y : H) : Prop :=
  x ∈ effectiveDomain f ∧
    ∃ ε > (0 : ℝ), ∀ ⦃α : ℝ⦄, α ∈ Set.Ioc (0 : ℝ) ε →
      f.asEReal (x + α • y) < f.asEReal x

end ERealFunction
