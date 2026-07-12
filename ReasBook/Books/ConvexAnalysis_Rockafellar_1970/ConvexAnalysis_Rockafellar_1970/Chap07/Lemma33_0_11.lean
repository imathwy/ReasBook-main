import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_9
import ConvexAnalysis_Rockafellar_1970.Chap07.Lemma33_0_9

universe u v u' v' r

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma33.0.11 evaluates the convex pairing of the singleton-indicator slice
  attached to a map `T` at a point `u`.
- `core/canonical`: the owner-level singleton slice is `Bifunction.graphIndicator α T u`; the
  point-indicator pairing formula is upstream in `Lemma33_0_9`.
- `bridge/view`: the linear-map reading is a direct specialization of the map-level owner theorem.

Domain-style sampling used here:
- `Bifunction.graphIndicator` from `Chap06.Definition_6_29_9`;
- `indicator` notation `δ[α](x | C)` from `Chap01.Defintion_4_8_1`;
- `convex pairing` notation `⟪f, y⟫ᶠ` from `Chap07.Definition33_0_8`;
- pairing notation `⟪x, y⟫ₚ` from `Chap01.HasPairing`.

Primitive data vs derived API:
- primitive data: a map `T : U → X`, a point `u : U`, and a pairing point `y : Y`;
- codomain data: a pairing codomain `WithBotTop α` with the structure required by
  `convexConjugate`;
- derived API: the convex pairing value of the singleton-graph indicator slice.

Layer target: `source-facing` theorem surface over the canonical singleton-graph owner.
-/

namespace Bifunction

section ConvexGraphIndicator

variable {α : Type r} {U : Type u} {X : Type v} {Y : Type v'}
variable [AddGroup α] [ConditionallyCompleteLattice α]
variable [HasPairing X Y α]

-- Proof sketch: rewrite the slice using `graphIndicator_slice`; the result is exactly the
-- singleton-indicator pairing formula from `Lemma33_0_9`.
/-- Lemma33.0.11: the convex pairing of the singleton-graph indicator slice
attached to a map `T` equals the pairing value at `T u`. -/
theorem convexPairing_graphIndicator_eq_pairing
    (T : U → X) (u : U) (y : Y) :
    ⟪graphIndicator α T u, y⟫ᶠ = ⟪T u, y⟫ₚ := by
  simpa [graphIndicator_slice] using
    (Function.convexPairing_indicator_singleton (x := T u) (y := y))

end ConvexGraphIndicator

section ConcaveGraphIndicator

variable {X : Type u'} {I : Type v'} {Y : Type u} {α : Type r}
variable [AddGroup α] [ConditionallyCompleteLattice α]
variable [HasPairing X Y α]

/-- Swapped pairing used to read the concave branch in the natural argument order. -/
local instance : HasPairing Y X α :=
  HasPairing.swap

-- Proof sketch: rewrite the slice using `graphConcaveIndicator`; the result is exactly the
-- negative-singleton concave pairing formula from `Lemma33_0_9`.
/-- The concave pairing of the singleton-graph concave-indicator slice attached to a map `T`
equals the pairing value at `T i`, in the natural orientation of the concave branch. -/
theorem concavePairing_graphConcaveIndicator_eq_pairing
    (T : I → X) (i : I) (y : Y) :
    ⟪y, graphConcaveIndicator α T i⟫ᶜ = ⟪y, T i⟫ₚ := by
  rw [graphConcaveIndicator_slice]
  exact
    Function.concavePairing_negIndicator_singleton
      (x := T i) (y := y)

end ConcaveGraphIndicator

end Bifunction
