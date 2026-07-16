import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_4

noncomputable section

universe u v w

open scoped Rockafellar

namespace Function

/-!
Source/core/bridge triage:

- `source-facing`: Definition 33.0.8 introduces the textbook pairing-style notation
  `⟨f, y⟩ = ⟨y, f⟩ := f*(y)` for both the convex and concave conjugate branches.
- `core/canonical`: the owners already exist as `convexConjugate` and `concaveConjugate`,
  defined at the primitive pairing/supremum or pairing/infimum layers.
- `bridge/view`: this file adds only the textbook pairing notation surfaces, without introducing a
  new owner or a duplicate wrapper API.

Abstraction checks:
- no `ℝ^n` specialization;
- no `EReal`-specific codomain lock-in;
- no wrapper `def`/`abbrev` around an existing owner;
- domain-style sampling: `convexConjugate`, `convexConjugate_eq_iSup_pairing_sub`,
  `concaveConjugate`, `concaveConjugate_eq_iInf_pairing_sub`;
- the source's context-dependent bracket notation is represented in Lean by two explicit
  orientation-specific scoped notations, one for the convex branch and one for the concave
  branch.
-/

/- Definition33.0.8: the source conjugate-pairing notation is a bridge over the existing
conjugate owners. The convex branch is recalled here from `convexConjugate`; the concave branch is
recalled below from `concaveConjugate`, and the four scoped notation declarations implement the
two reading orders `⟨f, x⋆⟩ = ⟨x⋆, f⟩` in each branch. -/
recall convexConjugate

/- Concave branch owner reused for the infimum orientation of the same source notation. -/
recall concaveConjugate

section ConvexPairingNotation

variable {X : Type u} {Y : Type v} {L : Type w}

/- Pairing-style convex notation for the canonical owner value `convexConjugate f y`. -/
scoped[Rockafellar] notation "⟪" f ", " y "⟫ᶠ" => convexConjugate f y

/- Symmetric reading order for the same convex pairing owner. -/
scoped[Rockafellar] notation "⟪" y ", " f "⟫ᶠ" => convexConjugate f y

variable [SupSet L] [Sub L] [HasPairing X Y L]

variable (f : X → L) (y : Y)

/-- Forward-order convex pairing notation is exactly the canonical conjugate value. -/
@[simp] theorem convexPairing_eq_conjugate :
    ⟪f, y⟫ᶠ = f⋆ y :=
  rfl

/-- Swapped-order convex pairing notation is exactly the canonical conjugate value. -/
@[simp] theorem convexPairing_swap_eq_conjugate :
    ⟪y, f⟫ᶠ = f⋆ y :=
  rfl

/-- Definition33.0.8 source surface: the two reading orders of convex pairing notation coincide. -/
@[simp] theorem convexPairing_swap :
    ⟪y, f⟫ᶠ = ⟪f, y⟫ᶠ :=
  rfl

/-- Convex pairing notation inherits the canonical supremum formula. -/
theorem convexPairing_eq_iSup_pairing_sub :
    ⟪f, y⟫ᶠ = ⨆ x : X, ⟪x, y⟫ₚ - f x := by
  simpa using (convexConjugate_eq_iSup_pairing_sub (f := f) (y := y))

/-- Swapped convex pairing notation inherits the same supremum formula. -/
theorem convexPairing_swap_eq_iSup_pairing_sub :
    ⟪y, f⟫ᶠ = ⨆ x : X, ⟪x, y⟫ₚ - f x := by
  simpa [convexPairing_swap] using (convexPairing_eq_iSup_pairing_sub (f := f) (y := y))

end ConvexPairingNotation

section ConcavePairingNotation

variable {X : Type u} {Y : Type v} {L : Type w}

/- Pairing-style concave notation for the canonical owner value `concaveConjugate g y`. -/
scoped[Rockafellar] notation "⟪" g ", " y "⟫ᶜ" => concaveConjugate g y

/- Symmetric reading order for the same concave pairing owner. -/
scoped[Rockafellar] notation "⟪" y ", " g "⟫ᶜ" => concaveConjugate g y

variable [InfSet L] [Sub L] [HasPairing X Y L]

variable (g : X → L) (y : Y)

/-- Forward-order concave pairing notation is exactly the canonical concave conjugate value. -/
@[simp] theorem concavePairing_eq_conjugate :
    ⟪g, y⟫ᶜ = g∗ y :=
  rfl

/-- Swapped-order concave pairing notation is exactly the canonical concave conjugate value. -/
@[simp] theorem concavePairing_swap_eq_conjugate :
    ⟪y, g⟫ᶜ = g∗ y :=
  rfl

/-- Definition33.0.8 source surface: the two reading orders of concave pairing notation coincide.
-/
@[simp] theorem concavePairing_swap :
    ⟪y, g⟫ᶜ = ⟪g, y⟫ᶜ :=
  rfl

/-- Concave pairing notation inherits the canonical infimum formula. -/
theorem concavePairing_eq_iInf_pairing_sub :
    ⟪g, y⟫ᶜ = ⨅ x : X, ⟪x, y⟫ₚ - g x := by
  simpa using (concaveConjugate_eq_iInf_pairing_sub (g := g) (y := y))

/-- Swapped concave pairing notation inherits the same infimum formula. -/
theorem concavePairing_swap_eq_iInf_pairing_sub :
    ⟪y, g⟫ᶜ = ⨅ x : X, ⟪x, y⟫ₚ - g x := by
  simpa [concavePairing_swap] using (concavePairing_eq_iInf_pairing_sub (g := g) (y := y))

end ConcavePairingNotation

end Function
