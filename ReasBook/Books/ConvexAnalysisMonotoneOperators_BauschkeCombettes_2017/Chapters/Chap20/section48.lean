import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_20_48 (from Chap20) -/
namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Theorem 20.48 records the maximal monotonicity of `∂ f`, obtained in the text
  via the autoconjugate route through Corollary 20.47.
- `core/canonical`: the owner theorem is
  `subdifferential_isMaximallyMonotone_of_mem_gammaZero`.
- `bridge/view`: the autoconjugate argument is an alternative proof route for the same owner
  theorem, not a second public owner. -/

/- Theorem 20.48: the autoconjugate proof route recovers exactly the canonical owner theorem from
Theorem 20.25 stating that, for `f ∈ Γ₀(ℋ)`, the subdifferential `∂ f` is maximally monotone. -/
recall subdifferential_isMaximallyMonotone_of_mem_gammaZero

end ERealFunction
