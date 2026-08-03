import BauschkeLean.Chap20.Theorem_20_25

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Theorem 20.48 records the maximal monotonicity of `∂ f`, obtained in the text
  via the autoconjugate route through Corollary 20.47.
- `core/canonical`: the owner theorem is
  `subdifferential_isMaximallyMonotone_of_mem_gammaZero`.
- `bridge/view`: the autoconjugate argument is only an alternative proof route for the same owner
  theorem, so this file should stay a pure recall rather than introducing a second public
  theorem.

Primitive data: none beyond the `Γ₀(H)` hypothesis already owned by
`subdifferential_isMaximallyMonotone_of_mem_gammaZero`.
Derived API: none; Corollary 20.47 explains the proof route, but Theorem 20.48 adds no new
canonical construction or companion interface. -/
-- Semantic recall note: `lean_leansearch` returned no direct stock theorem for this item, and
-- the verified project-local canonical owner is
-- `subdifferential_isMaximallyMonotone_of_mem_gammaZero`.

/- Theorem 20.48: Corollary 20.47 provides an alternative autoconjugate proof of Moreau's
canonical owner theorem `subdifferential_isMaximallyMonotone_of_mem_gammaZero`, so the numbered
item is a direct recall rather than a second local statement. -/
#check subdifferential_isMaximallyMonotone_of_mem_gammaZero

end ERealFunction
