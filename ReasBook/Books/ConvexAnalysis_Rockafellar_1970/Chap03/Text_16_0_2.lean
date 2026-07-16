import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

universe u v w

section

variable {X : Type u} {Y : Type v}
variable {α : Type w}
variable [ConditionallyCompleteLattice α] [One α]
variable [HasPairing Y X α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 16.0.2 says that the polar `Cᵒ` of a convex set is the `1`-sublevel set
  of its support function `δ*(· | C)`.
- `core/canonical`: the project already exposes this notion as the canonical owner definition
  `Set.polar`.
- `bridge/view`: Rockafellar's notation `δ*(x* | C)` is represented by `supportFunction C xStar`,
  and here the source sentence is exposed directly as a theorem at the generalized pairing layer.

Domain-style sampling used here:
- the project definition `Set.polar` from `Text_14_0_5`;
- the support-function owner `supportFunction`, via notation `δᵛ[WithBotTop α](· | C)`.

Primitive data vs derived API:
- primitive input: a set `C`;
- primitive owner: the already-defined polar set `Set.polar C`;
- derived/source-facing view: the textbook level-set description
  `{xStar | δᵛ[WithBotTop α](xStar | C) ≤ 1}`.

Layer target: `core/canonical`.

The source's convexity hypothesis is redundant for this bare identification, so the existing owner
is kept and only the source-facing bridge theorem is exposed.
-/

namespace Set

-- Proof sketch: unfold `Set.polar`; membership in a preimage of `Set.Iic (1 : WithBotTop α)` is
-- exactly the corresponding support-function inequality.
/-- Text 16.0.2 (membership form): a dual point is in `Cᵒ[α]` iff the support function of `C`
at that point is at most `1`. This is the source-facing sublevel-set sentence at the canonical
pairing/extended-codomain layer. -/
theorem mem_polar_iff_supportFunction_le_one {C : Set X} {xStar : Y} :
    xStar ∈ Cᵒ[α] ↔
      (δᵛ[WithBotTop α](xStar | C) : WithBotTop α) ≤ (1 : WithBotTop α) := by
  change
    (δᵛ[WithBotTop α](xStar | C) : WithBotTop α) ∈ Set.Iic (1 : WithBotTop α) ↔
      (δᵛ[WithBotTop α](xStar | C) : WithBotTop α) ≤ (1 : WithBotTop α)
  simp

-- Proof sketch: extensionality reduces set equality to the previous membership theorem.
/-- Text 16.0.2 (set form): `Cᵒ[α]` is exactly the `1`-sublevel set of `δᵛ[WithBotTop α](· | C)`. -/
theorem polar_eq_supportFunction_sublevel (C : Set X) :
    Cᵒ[α] = {xStar : Y | (δᵛ[WithBotTop α](xStar | C) : WithBotTop α) ≤ (1 : WithBotTop α)} := by
  ext xStar
  exact mem_polar_iff_supportFunction_le_one

end Set

end
