import ConvexAnalysis_Rockafellar_1970.Chap07.Lemma33_0_11

noncomputable section

universe u v u' v' s

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Lemma33.0.30 is the pointwise pairing equation for the singleton-graph
  indicator of a map and the corresponding singleton concave indicator of a dual companion map.
- `core/canonical`: the owner abstractions already present and available here are the Chapter 6
  singleton-graph indicator owners `graphIndicator 𝕜 T` and `graphConcaveIndicator 𝕜 T` from
  `Definition_6_29_9`, together with the Chapter 33 pairing notations `⟪·, ·⟫ᶠ` and `⟪·, ·⟫ᶜ`.
- `bridge/view`: linear-map uses are direct specializations of those map-level owners.

Domain-style sampling used here:
- `graphIndicator` and `graphConcaveIndicator` from `Chap06.Definition_6_29_9`;
- the pairing notations `⟪·, ·⟫ₚ`, `⟪·, ·⟫ᶠ`, and `⟪·, ·⟫ᶜ` from `Definition33_0_8`;
- the singleton-graph pairing owner theorems `convexPairing_graphIndicator_eq_pairing` and
  `concavePairing_graphConcaveIndicator_eq_pairing` from `Lemma33_0_11`;
- the Chapter 1 indicator owner `δ[α](x | C)` that underlies both singleton formulas.

API decision:
- the singleton-slice owners are reused directly from `Definition_6_29_9`, and the left-hand
  pairing evaluations are reused from the canonical Chapter 33 owner theorems
  `convexPairing_graphIndicator_eq_pairing` and
  `concavePairing_graphConcaveIndicator_eq_pairing`;
- the public item stays at the pointwise pairing-equation layer, which is the source-faithful
  statement available at the current pairing abstraction level;
- no owner-level equality for `adjoint` is kept here, because that stronger identification
  needs extra duality hypotheses not present in this file.
-/

/-! Pairing-compatibility owner for map companions used by the singleton-graph equation. -/

section PairingCompanion

variable {α : Type s}
variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [HasPairing U UStar α] [HasPairing X XStar α]

/-- Global pairing compatibility of a map `A` and a dual companion map `Astar`. -/
def IsPairingCompanion
    (A : U → X) (Astar : XStar → UStar) : Prop :=
  ∀ (u : U) (xStar : XStar),
    ⟪A u, xStar⟫ₚ = ⟪u, Astar xStar⟫ₚ

end PairingCompanion

section PairingReduction

variable {α : Type s}
variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [AddGroup α] [ConditionallyCompleteLattice α]
variable [HasPairing U UStar α] [HasPairing X XStar α]

local instance : HasPairing UStar U α := HasPairing.swap

-- Proof sketch: both pairing terms are already evaluated canonically by the graph-indicator owner
-- theorems from `Lemma33_0_11`, so the statement reduces immediately to the underlying pairing
-- equality.
/-- Lemma33.0.30: the chapter pairing equation for the singleton-indicator bifunction and the
corresponding singleton concave-indicator bifunction is equivalent to the classical pairing
relation written in the natural orientation of the concave branch:
`⟪A u, x⋆⟫ = ⟪u, Astar x⋆⟫`. -/
theorem pairingEquation_graphIndicator_iff_pairing
    (A : U → X) (Astar : XStar → UStar) (u : U) (xStar : XStar) :
    (⟪graphIndicator α A u, xStar⟫ᶠ = ⟪u, graphConcaveIndicator α Astar xStar⟫ᶜ) ↔
      ⟪A u, xStar⟫ₚ = ⟪u, Astar xStar⟫ₚ := by
  constructor
  · intro hEq
    rw [convexPairing_graphIndicator_eq_pairing (T := A) (u := u) (y := xStar)] at hEq
    rw [concavePairing_graphConcaveIndicator_eq_pairing (T := Astar) (i := xStar)
      (y := u)] at hEq
    exact WithBotTop.coe_injective hEq
  · intro hPair
    have hPair' :
        ((⟪A u, xStar⟫ₚ : α) : WithBotTop α) =
          ((⟪u, Astar xStar⟫ₚ : α) : WithBotTop α) :=
      congrArg (fun t : α ↦ (t : WithBotTop α)) hPair
    rw [convexPairing_graphIndicator_eq_pairing (T := A) (u := u) (y := xStar)]
    rw [concavePairing_graphConcaveIndicator_eq_pairing (T := Astar) (i := xStar)
      (y := u)]
    exact hPair'

-- Proof sketch: apply the pointwise bridge theorem at `(u, xStar)` with the global companion
-- hypothesis.
/-- Global compatibility form of Lemma33.0.30: if `Astar` is a pairing companion of `A`, then the
singleton-graph pairing equation holds at every point. -/
theorem pairingEquation_graphIndicator_of_isPairingCompanion
    (A : U → X) (Astar : XStar → UStar)
    (hA : IsPairingCompanion A Astar)
    (u : U) (xStar : XStar) :
    ⟪graphIndicator α A u, xStar⟫ᶠ = ⟪u, graphConcaveIndicator α Astar xStar⟫ᶜ := by
  exact (pairingEquation_graphIndicator_iff_pairing A Astar u xStar).2 (hA u xStar)

end PairingReduction

end Bifunction
