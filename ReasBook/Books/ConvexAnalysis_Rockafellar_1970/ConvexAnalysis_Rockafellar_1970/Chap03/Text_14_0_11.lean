import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_5

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.11 says that polarity reverses inclusion for convex sets.
- `core/canonical`: the owner abstraction already present in the project is the source-facing set
  polar `Set.polar`, and the canonical order-theoretic formulation of the source sentence is the
  predicate `Antitone`.
- `bridge/view`: the textbook conclusion `C1ᵒ ⊇ C2ᵒ` is rendered canonically by the owner-side
  statement that `Set.polar` is antitone.

Domain-style sampling used here:
- `Set.polar` from `Text_14_0_5`;
- `Set.mem_polar_iff` from `Text_14_0_5`;
- the standard order-theoretic predicate `Antitone`.

Primitive data vs derived API:
- primitive owner: the map `Set.polar : Set E → Set E`;
- derived source-facing consequence: the reverse inclusion between the polars of comparable sets.

The source's closedness, convexity, and origin-membership hypotheses are redundant for this order
reversal, and the owner `Set.polar` already lives on arbitrary real inner-product spaces. The Lean
statement is therefore given at that ambient owner level instead of the display model `ℝ^n`.

Layer target: `core/canonical`.
-/

namespace Set

-- Proof sketch: if `xStar ∈ polar C2`, then `mem_polar_iff` gives
-- `⟪x, xStar⟫ ≤ 1` for every `x ∈ C2`. Along an inclusion `C1 ⊆ C2`, the same inequalities hold
-- for every `x ∈ C1`, so `xStar ∈ polar C1`. This is exactly the statement that `polar`
-- is antitone.
local notation "polar" => (Set.polar (α := ℝ) : Set E → Set E)

/-- Text 14.0.11: polarity is order-inverting. Equivalently, the source-facing polar map is
antitone. The source states this for closed convex sets containing the origin, but those
hypotheses are unnecessary for the inclusion itself. -/
theorem polar_antitone : Antitone polar := by
  intro C1 C2 hC xStar hxStar
  rw [mem_polar_iff] at hxStar ⊢
  exact fun x hx ↦ hxStar x (hC hx)

end Set

end
