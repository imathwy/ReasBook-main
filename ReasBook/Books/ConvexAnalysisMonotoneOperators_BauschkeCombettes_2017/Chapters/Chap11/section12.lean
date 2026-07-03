import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_11_12 (from Chap11) -/
universe u

namespace ERealFunction

variable {H : Type u} [SeminormedAddCommGroup H]

-- Proof sketch: if some lower level set is unbounded, choose a sequence in it with norms tending
-- to `+∞`; along that sequence the function values stay below the same real threshold, so `f` is
-- not coercive. Conversely, if every real lower level set is bounded and `‖xₙ‖ → +∞`, then for
-- each real threshold `ξ` the tail of `xₙ` eventually leaves `lowerLevelSet f ξ`, which forces
-- `f xₙ → +∞`.
/-- Proposition 11.12: an extended-real-valued function is coercive if and only if each of its
real lower level sets is bounded. -/
theorem coercive_iff_bounded_lowerLevelSet (f : H → EReal) :
    Coercive f ↔ ∀ ξ : ℝ, Bornology.IsBounded (lowerLevelSet f ξ) := by
  rw [Coercive, EReal.tendsto_nhds_top_iff_real]
  constructor
  · intro hf ξ
    refine (Bornology.isBounded_def).2 ?_
    change {x : H | ¬f x ≤ (ξ : EReal)} ∈ Bornology.cobounded H
    simpa [not_le] using hf ξ
  · intro h ξ
    have hξ : (lowerLevelSet f ξ)ᶜ ∈ Bornology.cobounded H :=
      (Bornology.isBounded_def).1 (h ξ)
    change {x : H | ¬f x ≤ (ξ : EReal)} ∈ Bornology.cobounded H at hξ
    change {x : H | (ξ : EReal) < f x} ∈ Bornology.cobounded H
    simpa [not_le] using hξ

end ERealFunction
