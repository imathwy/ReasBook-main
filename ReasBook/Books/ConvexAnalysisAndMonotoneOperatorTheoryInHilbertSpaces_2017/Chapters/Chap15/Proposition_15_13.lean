import Mathlib
import BauschkeLean.Chap15.FenchelSameSpaceAttainment

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

universe u

namespace ERealFunction

section FenchelDuality

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 15.13 is the same-space Fenchel-duality attainment statement under
  the textbook regularity hypothesis `0 ∈ sri (effectiveDomain f - effectiveDomain g)`.
- `core/canonical`: the owner declarations are `fenchelDualObjective`, `primalOptimalValue`, and
  `Argmin`.
- `bridge/view`: this file is now only the public wrapper around the shared same-space owner
  theorem used by both Corollary 15.15 and the Chapter 15 product-graph development.
-/

-- Proof sketch: consume the shared same-space owner theorem directly, so the public proposition
-- keeps its statement while the actual owner lives upstream of both downstream adapters.
/-- Proposition 15 13: if `f, g ∈ Γ₀(H)` and
`0 ∈ sri (dom f - dom g)`, then the primal optimal value is the negative of the minimum of the
Fenchel dual objective `u ↦ f^*(-u) + g^*(u)`. -/
theorem exists_mem_argmin_fenchelDualObjective_eq_neg_primalOptimalValue_of_zero_mem_sri_sub_effectiveDomain
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    ∃ u ∈ Argmin (fenchelDualObjective f g),
      primalOptimalValue f g = -(fenchelDualObjective f g u) := by
  -- Route correction: this proposition no longer owns the same-space attainment proof, so it
  -- stays a thin adapter and avoids importing the later composite-duality theorem file.
  simpa using
    exists_mem_argmin_fenchelDualObjective_eq_neg_primalOptimalValue_of_zero_mem_sri_sub_effectiveDomain_shared
      f g hf hg hsri

end FenchelDuality

end ERealFunction
