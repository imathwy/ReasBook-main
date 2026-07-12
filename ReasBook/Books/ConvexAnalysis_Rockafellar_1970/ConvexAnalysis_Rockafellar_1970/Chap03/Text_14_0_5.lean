import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_0_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

universe u v w

section

variable {X : Type u} {Y : Type v}
variable {α : Type w}
variable [Preorder α] [SupSet α] [One α]
variable [HasPairing Y X α]

/-
Source/core/bridge triage:
- `source-facing`: Text 14.0.5 defines the polar `Cᵒ[α]` by the support-function inequality
  `δ*(xStar | C) ≤ 1`.
- `core/canonical`: the owner abstraction is the support-function `1`-sublevel preimage.
- `bridge/view`: pointwise membership inequalities are derived from this owner by
  `supportFunction_def`.

Primitive data vs derived API:
- primitive owner: `Set.polar`, now at the pairing layer `C : Set X ↦ Set Y` rather than the
  over-concrete self-dual surface `Set E → Set E`;
- derived API: the pointwise membership criterion and closure invariance.
-/

namespace Set

/-- Text 14.0.5: the polar of a subset `C` is the support-function `1`-sublevel set. The owner is
kept at the pairing layer `Set X → Set Y`: only the primal set `C : Set X` and dual points
`xStar : Y` are primitive data. -/
def polar (α : Type w) [Preorder α] [SupSet α] [One α] [HasPairing Y X α]
    (C : Set X) : Set Y :=
  (δᵛ(· | C) : Y → WithTopBot α) ⁻¹' Set.Iic (1 : WithTopBot α)

scoped[Rockafellar] notation:max C "ᵒ[" 𝕜 "]" => (Set.polar 𝕜 C)

open scoped Rockafellar

end Set

end

section

variable {X : Type u} {Y : Type v}
variable {α : Type w}
variable [ConditionallyCompleteLattice α] [One α]
variable [HasPairing Y X α]

namespace Set

/-- Primitive support-function membership form of `Cᵒ[α]`: by definition,
`xStar ∈ Cᵒ[α]` iff `⟪xStar, x⟫ₚ ≤ 1` for every `x ∈ C`. -/
@[simp] theorem mem_polar_iff {C : Set X} {xStar : Y} :
    xStar ∈ Cᵒ[α] ↔ ∀ x ∈ C, (⟪xStar, x⟫ₚ : α) ≤ (1 : α) := by
  rw [polar]
  change
    (δᵛ(xStar | C) : WithTopBot α) ≤ (1 : WithTopBot α) ↔
      ∀ x ∈ C, (⟪xStar, x⟫ₚ : α) ≤ (1 : α)
  rw [supportFunction_def]
  constructor
  · intro hx x hxC
    have hxWithTopBot : (⟪xStar, x⟫ₚ : WithTopBot α) ≤ (1 : WithTopBot α) := by
      exact (le_iSup (fun z : C ↦ (⟪xStar, (z : X)⟫ₚ : WithTopBot α)) ⟨x, hxC⟩).trans hx
    have hxWithBot : ((⟪xStar, x⟫ₚ : α) : WithBot α) ≤ (1 : WithBot α) :=
      (WithTop.coe_le_coe).1 hxWithTopBot
    exact (WithBot.coe_le_coe).1 hxWithBot
  · intro hx
    refine iSup_le ?_
    intro x
    have hxWithBot : ((⟪xStar, (x : X)⟫ₚ : α) : WithBot α) ≤ (1 : WithBot α) :=
      (WithBot.coe_le_coe).2 (hx x x.2)
    exact (WithTop.coe_le_coe).2 hxWithBot

end Set

end

section

open scoped Rockafellar

variable {X : Type u} {Y : Type v} {α : Type w}
variable [ConditionallyCompleteLattice α] [One α]
variable [HasPairing Y X α] [HasPairing X Y α] [HasPairingSwap X Y α]

namespace Set

/-- Membership in `Cᵒ[α]` is equivalent to the pointwise inequality `⟪x, xStar⟫ ≤ 1` for every
`x ∈ C`, written in the swapped pairing orientation `(X, Y)`. -/
-- Proof sketch: first use the primitive pairing-orientation characterization
-- `mem_polar_iff`, then rewrite `⟪xStar, x⟫` as `⟪x, xStar⟫` via symmetry of the
-- bidirectional pairing (`HasPairingSwap`).
theorem mem_polar_iff_swap {C : Set X} {xStar : Y} :
    xStar ∈ Cᵒ[α] ↔ ∀ x ∈ C, (⟪x, xStar⟫ₚ : α) ≤ (1 : α) := by
  constructor
  · intro hx x hxC
    have hpair := (Set.mem_polar_iff (C := C) (xStar := xStar)).1 hx x hxC
    calc
      (⟪x, xStar⟫ₚ : α) = ⟪xStar, x⟫ₚ := HasPairingSwap.pairing_swap (x := x) (y := xStar)
      _ ≤ (1 : α) := hpair
  · intro hx
    refine (Set.mem_polar_iff (C := C) (xStar := xStar)).2 ?_
    intro x hxC
    have hsrc : (⟪x, xStar⟫ₚ : α) ≤ (1 : α) := hx x hxC
    calc
      (⟪xStar, x⟫ₚ : α) = ⟪x, xStar⟫ₚ := (HasPairingSwap.pairing_swap (x := x) (y := xStar)).symm
      _ ≤ (1 : α) := hsrc

end Set

end

section

open scoped Rockafellar

variable {E : Type u}
variable {Y : Type v}
variable {α : Type w}
variable [TopologicalSpace E]
variable [ConditionallyCompleteLattice α] [One α]
variable [TopologicalSpace α] [OrderClosedTopology α]
variable [HasPairing E Y α]
variable [HasContinuousPairing E Y α]

namespace Set

-- Use the canonical swapped pairing instance induced by the primal/dual pairing `HasPairing E Y α`.
local instance : HasPairing Y E α :=
  HasPairing.swap (X := E) (Y := Y) (L := α)

/-- Passing from `C` to `closure C` does not change its polar. -/
theorem polar_eq_of_closure_eq {C D : Set E} (hCD : closure C = closure D) :
    (Cᵒ[α] : Set Y) = Dᵒ[α] := by
  ext xStar
  have hsf :
      (δᵛ(xStar | C) : WithTopBot α) = (δᵛ(xStar | D) : WithTopBot α) := by
    exact congrArg (fun f : Y → WithTopBot α => f xStar)
      (supportFunction_eq_of_closure_eq (C := C) (D := D) hCD)
  simp [Set.polar, hsf]

/-- Passing from `C` to `closure C` does not change its polar. -/
@[simp] theorem polar_closure (C : Set E) :
    ((closure C)ᵒ[α] : Set Y) = Cᵒ[α] := by
  simpa using
    (polar_eq_of_closure_eq (C := C) (D := closure C) (by simp)).symm

end Set

end
