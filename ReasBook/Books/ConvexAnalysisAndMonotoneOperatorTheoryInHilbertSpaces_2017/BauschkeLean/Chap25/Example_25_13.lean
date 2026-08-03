import BauschkeLean.Chap22.Proposition_22_14
import BauschkeLean.Chap25.Proposition_25_12

open scoped InnerProductSpace SetValuedOperator

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Example 25.13 states the chapter's subdifferential example.
- `core/canonical`: the owner abstractions are
  `SetValuedOperator.IsCyclicallyMonotone`, `SetValuedOperator.IsNCyclicallyMonotone _ 3`, and
  `SetValuedOperator.IsThreeStarMonotone`.
- `bridge/view`: `subdifferential_isCyclicallyMonotone` and
  `SetValuedOperator.IsNCyclicallyMonotone.isThreeStarMonotone` already expose the needed
  implications, so the example should compose them directly instead of introducing any local
  wrapper API. -/

/-- Example 25.13: if `f` is proper, then its subdifferential `∂ f` is `3*`
monotone. -/
theorem subdifferential_isThreeStarMonotone
    {f : H → EReal} (hf : IsProper f) :
    (∂ f).IsThreeStarMonotone :=
  ((subdifferential_isCyclicallyMonotone hf).isNCyclicallyMonotone
    (by decide)).isThreeStarMonotone

end ERealFunction
