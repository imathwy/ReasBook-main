import BauschkeLean.Chap20.Theorem_20_25

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Theorem 21.2 records the maximal monotonicity of the subdifferential `∂ f`
  for `f ∈ Γ₀(H)`.
- `core/canonical`: the owner theorem is
  `subdifferential_isMaximallyMonotone_of_mem_gammaZero`.
- `bridge/view`: none; this numbered item adds no new source-level construction or companion
  interface beyond recalling the Chapter 20 owner.

Primitive data: none beyond the `Γ₀(H)` hypothesis already owned by
`subdifferential_isMaximallyMonotone_of_mem_gammaZero`.
Derived API: none; the numbered item is only a recall of the existing owner theorem. -/
/- Theorem 21.2. If `f ∈ Γ₀(H)`, then the subdifferential `∂ f` is maximally monotone.

This item is a direct recall of the canonical owner theorem
`subdifferential_isMaximallyMonotone_of_mem_gammaZero`. -/
#check subdifferential_isMaximallyMonotone_of_mem_gammaZero

end ERealFunction
