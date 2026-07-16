import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_8

noncomputable section

universe u v v' w

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Definition33.0.10 introduces the slice pairing of a bifunction `F` with a dual
  variable `x⋆`, namely the conjugate pairing of the function slice `F u`.
- `core/canonical`: the project already owns the function-level pairing surfaces
  `convexConjugate`, `concaveConjugate`, and their pointwise `iSup`/`iInf` formula theorems.
- `bridge/view`: a bifunction is only a family of slices, so this item is a pure slice-wise reuse
  of the existing conjugate API, not a second bifunction owner. The correct public surface for
  this numbered item is therefore direct canonical recall/use plus thin slice-specialization bridge
  theorems over those existing owners, without introducing a new bifunction owner.

Domain-style sampling used here:
- `convexConjugate` together with `convexConjugate_eq_iSup_pairing_sub`;
- `concaveConjugate` together with `concaveConjugate_eq_iInf_pairing_sub`;
- the Chapter 33 notation bridge `⟪f, y⟫ᶠ` / `⟪g, y⟫ᶜ` from `Definition33_0_8`.

Layer target: `bridge/view`.
-/

/- Definition33.0.10: at a fixed slice, the source pairing formulas are exactly the existing
conjugate owners and their specification theorems; no additional bifunction-level owner or wrapper
API is introduced here. -/
recall convexConjugate

/- The convex slice-pairing formula is already the canonical owner specification theorem. -/
recall convexConjugate_eq_iSup_pairing_sub

/- The concave slice-pairing owner is already present in the project. -/
recall concaveConjugate

/- The concave slice-pairing formula is already the canonical owner specification theorem. -/
recall concaveConjugate_eq_iInf_pairing_sub

section ConvexSlicePairing

variable {U : Type u} {X : Type v} {Y : Type v'} {L : Type w}
variable [Sub L] [SupSet L] [HasPairing X Y L]

variable (F : U → X → L) (u : U) (y : Y)

/-- Definition33.0.10, convex branch: the slice pairing of a bifunction is exactly the canonical
Fenchel-conjugate supremum formula applied to the slice `F u`. -/
theorem convexPairing_slice_eq_iSup_pairing_sub :
    ⟪F u, y⟫ᶠ = ⨆ x : X, ⟪x, y⟫ₚ - F u x := by
  simpa using (convexConjugate_eq_iSup_pairing_sub (F u) y)

end ConvexSlicePairing

section ConcaveSlicePairing

variable {U : Type u} {X : Type v} {Y : Type v'} {L : Type w}
variable [Sub L] [InfSet L] [HasPairing X Y L]

variable (F : U → X → L) (u : U) (y : Y)

/-- Definition33.0.10, concave branch: the slice pairing of a bifunction is exactly the canonical
concave-conjugate infimum formula applied to the slice `F u`. -/
theorem concavePairing_slice_eq_iInf_pairing_sub :
    ⟪F u, y⟫ᶜ = ⨅ x : X, ⟪x, y⟫ₚ - F u x := by
  simpa using (concaveConjugate_eq_iInf_pairing_sub (F u) y)

end ConcaveSlicePairing

end Bifunction
