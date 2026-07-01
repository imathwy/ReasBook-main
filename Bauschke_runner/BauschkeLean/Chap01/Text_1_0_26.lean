import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Text 1.0.26: the extended real line is formalized by the canonical type `EReal` of real
numbers with adjoined bottom and top elements `⊥` and `⊤`, equipped with the extended order;
the textbook's conventions about indeterminate arithmetic expressions are handled separately when
needed. -/
recall EReal : Type

namespace EReal

/-- Every real number lies strictly between `-∞` and `+∞` in the extended real line. -/
theorem real_strictly_between_infinities (ξ : ℝ) :
    (⊥ : EReal) < (ξ : EReal) ∧ (ξ : EReal) < ⊤ := by
  exact ⟨bot_lt_coe ξ, coe_lt_top ξ⟩

end EReal
