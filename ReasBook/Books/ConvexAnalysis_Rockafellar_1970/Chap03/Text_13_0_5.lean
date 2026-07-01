import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Basic
import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_2_0_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_3
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_0_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

section

variable {X Y α : Type*} [TopologicalSpace X]
variable [ConditionallyCompleteLattice α] [TopologicalSpace α] [OrderClosedTopology α]
variable [HasPairing X Y α] [HasContinuousPairing X Y α]

-- Canonical swapped pairing view used by support-function owners on the dual side.
local instance : HasPairing Y X α :=
  HasPairing.swap (X := X) (Y := Y) (L := α)
local instance : HasPairingSwap X Y α where
  pairing_swap _ _ := rfl
local instance : HasPairing X Y (WithTopBot α) := instHasPairingWithBotTop
local instance : HasPairing Y X (WithTopBot α) := instHasPairingWithBotTop

/-
Source/core/bridge triage:
- `source-facing`: Text 13.0.5 states that the support function of a convex set is unchanged by
  passing either to its closure or to its relative interior.
- `core/canonical`: the owner abstractions are the project support function `supportFunction`, the
  closure operator `closure`, and (for the second theorem) the convexity/relative-interior owners.
- `bridge/view`: Rockafellar's `δ*(x⋆ | C)` is represented by `supportFunction C xStar`.
- Primitive data vs derived API: the closure identity is derived directly from the owner set
  `C : Set X`, so its public API should not store a redundant convexity hypothesis.
- Domain-style sampling used here: `supportFunction`,
  `subset_closedHalfSpaceLE_withTopBot_iff_supportFunction_le`, and
  `closedHalfSpaceLE_closed` (used through a `WithTopBot` bridge lemma).
- Layer target: the closure form is the pairing/topological owner statement, not an
  inner-product-space specialization.
-/

/-- Closedness bridge for `WithTopBot` thresholds: the half-space cut
by `⟪x, xStar⟫ₚ ≤ β` is closed for every `β : WithTopBot α`. -/
theorem closedHalfSpaceLE_closed_withTopBot (xStar : Y) (β : WithTopBot α) :
    IsClosed (closedHalfSpaceLE (X := X) xStar β) := by
  cases β with
  | none =>
      change IsClosed (closedHalfSpaceLE (X := X) xStar (⊤ : WithTopBot α))
      have hEq : closedHalfSpaceLE (X := X) xStar (⊤ : WithTopBot α) = (Set.univ : Set X) := by
        ext x
        constructor
        · intro _
          trivial
        · intro _
          exact (mem_closedHalfSpaceLE_iff (X := X)).2 le_top
      simp [hEq]
  | some β' =>
      cases β' with
      | bot =>
          change IsClosed (closedHalfSpaceLE (X := X) xStar (⊥ : WithTopBot α))
          have hEq : closedHalfSpaceLE (X := X) xStar (⊥ : WithTopBot α) = (∅ : Set X) := by
            ext x
            constructor
            · intro hx
              have hxTop : (⟪x, xStar⟫ₚ : WithTopBot α) ≤ (⊥ : WithTopBot α) :=
                (mem_closedHalfSpaceLE_iff (X := X)).1 hx
              have hxBot : ((⟪x, xStar⟫ₚ : α) : WithBot α) ≤ (⊥ : WithBot α) :=
                (WithTop.coe_le_coe).1 hxTop
              exact (WithBot.not_coe_le_bot (⟪x, xStar⟫ₚ) hxBot).elim
            · intro hx
              exact False.elim hx
          simp [hEq]
      | coe a =>
          change IsClosed (closedHalfSpaceLE (X := X) xStar (((a : α) : WithBot α) : WithTopBot α))
          have hEq :
              closedHalfSpaceLE (X := X) xStar (((a : α) : WithBot α) : WithTopBot α) =
                closedHalfSpaceLE (X := X) (Y := Y) (R := α) xStar a := by
            ext x
            constructor
            · intro hx
              have hxTop : (⟪x, xStar⟫ₚ : WithTopBot α) ≤ (((a : α) : WithBot α) : WithTopBot α) :=
                (mem_closedHalfSpaceLE_iff (X := X)).1 hx
              have hxBot : ((⟪x, xStar⟫ₚ : α) : WithBot α) ≤ ((a : α) : WithBot α) :=
                (WithTop.coe_le_coe).1 hxTop
              have hxα : (⟪x, xStar⟫ₚ : α) ≤ a := (WithBot.coe_le_coe).1 hxBot
              exact (mem_closedHalfSpaceLE_iff (X := X)).2 hxα
            · intro hx
              have hxα : (⟪x, xStar⟫ₚ : α) ≤ a := (mem_closedHalfSpaceLE_iff (X := X)).1 hx
              have hxBot : ((⟪x, xStar⟫ₚ : α) : WithBot α) ≤ ((a : α) : WithBot α) :=
                (WithBot.coe_le_coe).2 hxα
              have hxTop :
                  (((⟪x, xStar⟫ₚ : α) : WithBot α) : WithTopBot α) ≤
                    ((((a : α) : WithBot α) : WithTopBot α)) :=
                (WithTop.coe_le_coe).2 hxBot
              exact (mem_closedHalfSpaceLE_iff (X := X)).2 hxTop
          simpa [hEq] using (closedHalfSpaceLE_closed (X := X) (Y := Y) (R := α) xStar a)

/-- Text 13.0.5 (closure form): passing from a set `C` to `closure C` does not change its support
function. -/

-- Proof sketch: monotonicity gives `supportFunction C ≤ supportFunction (closure C)`. For the
-- reverse inequality, apply Text 13.0.3 at threshold
-- `β := δᵛ[WithTopBot α](xStar | C)`, which gives `C ⊆ closedHalfSpaceLE xStar β`. Since that
-- half-space is closed, `closure C` is still inside it, and Text 13.0.3 again yields
-- `δᵛ[WithTopBot α](xStar | closure C) ≤ β`.
theorem supportFunction_closure {C : Set X} :
    (δᵛ(· | closure C) : Y → WithTopBot α) =
      (δᵛ(· | C) : Y → WithTopBot α) := by
  ext xStar
  refine le_antisymm ?_ ?_
  · have hCsubset : C ⊆ closedHalfSpaceLE xStar ((δᵛ(xStar | C) : WithTopBot α)) :=
      (subset_closedHalfSpaceLE_withTopBot_iff_supportFunction_le
        C xStar ((δᵛ(xStar | C) : WithTopBot α))).2 le_rfl
    have hclosureSubset :
        closure C ⊆ closedHalfSpaceLE xStar ((δᵛ(xStar | C) : WithTopBot α)) :=
      closure_minimal hCsubset
        (closedHalfSpaceLE_closed_withTopBot xStar ((δᵛ(xStar | C) : WithTopBot α)))
    exact
      (subset_closedHalfSpaceLE_withTopBot_iff_supportFunction_le
        (closure C) xStar ((δᵛ(xStar | C) : WithTopBot α))).1 hclosureSubset
  · rw [supportFunction_def, supportFunction_def]
    refine iSup_le ?_
    intro y
    exact le_iSup_of_le ⟨y, subset_closure y.2⟩ le_rfl

/-- Primitive closure bridge: if two sets have the same closure, then they have the same support
function. -/
theorem supportFunction_eq_of_closure_eq {C D : Set X} (hCD : closure C = closure D) :
    (δᵛ(· | C) : Y → WithTopBot α) =
      (δᵛ(· | D) : Y → WithTopBot α) := by
  calc
    (δᵛ(· | C) : Y → WithTopBot α) =
        (δᵛ(· | closure C) : Y → WithTopBot α) := by
      simpa using (supportFunction_closure (C := C)).symm
    _ = (δᵛ(· | closure D) : Y → WithTopBot α) := by
      rw [hCD]
    _ = (δᵛ(· | D) : Y → WithTopBot α) := supportFunction_closure (C := D)

end

section

variable {𝕜 X Y α : Type*}
variable [Ring 𝕜]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [ConditionallyCompleteLattice α] [TopologicalSpace α] [OrderClosedTopology α]
variable [HasPairing X Y α] [HasContinuousPairing X Y α]

-- Canonical swapped pairing view used by support-function owners on the dual side.
local instance : HasPairing Y X α :=
  HasPairing.swap (X := X) (Y := Y) (L := α)
local instance : HasPairingSwap X Y α where
  pairing_swap _ _ := rfl
local instance : HasPairing X Y (WithTopBot α) := instHasPairingWithBotTop
local instance : HasPairing Y X (WithTopBot α) := instHasPairingWithBotTop

/-- Primitive relative-interior bridge for Text 13.0.5: if `closure (ri[𝕜](C)) = closure C`,
then passing from `C` to `ri[𝕜](C)` does not change the support function. -/
theorem supportFunction_ri_of_closure_eq
    {C : Set X} (hri : closure (ri[𝕜](C)) = closure C) :
    (δᵛ(· | ri[𝕜](C)) : Y → WithTopBot α) =
      (δᵛ(· | C) : Y → WithTopBot α) := by
  exact supportFunction_eq_of_closure_eq hri

end

section

variable {𝕜 X Y α : Type*}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace 𝕜]
variable [ConditionallyCompleteLattice α] [TopologicalSpace α] [OrderClosedTopology α]
variable [HasPairing X Y α] [HasContinuousPairing X Y α]
variable [FiniteDimensional 𝕜 X]

-- Canonical swapped pairing view used by support-function owners on the dual side.
local instance : HasPairing Y X α :=
  HasPairing.swap (X := X) (Y := Y) (L := α)
local instance : HasPairingSwap X Y α where
  pairing_swap _ _ := rfl
local instance : HasPairing X Y (WithTopBot α) := instHasPairingWithBotTop
local instance : HasPairing Y X (WithTopBot α) := instHasPairingWithBotTop

omit [LinearOrder 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Finite-dimensional intrinsic bridge: equality of intrinsic closures of `ri[𝕜](C)` and `C`
implies support-function equality between those sets. -/
theorem supportFunction_ri_of_intrinsicClosure_eq {C : Set X}
    (hri : intrinsicClosure 𝕜 (ri[𝕜](C)) = intrinsicClosure 𝕜 C) :
    (δᵛ(· | ri[𝕜](C)) : Y → WithTopBot α) =
      (δᵛ(· | C) : Y → WithTopBot α) := by
  apply supportFunction_ri_of_closure_eq (C := C)
  simpa [intrinsicClosure_eq_closure 𝕜 (ri[𝕜](C)),
    intrinsicClosure_eq_closure 𝕜 C] using hri

namespace Convex

/-- Text 13.0.5 (relative-interior form): for a convex set `C`, passing from `C` to
`intrinsicInterior 𝕜 C` does not change its support function, with values in
`WithTopBot α`. -/
-- Proof sketch: use the intrinsic-closure form from Theorem 6.3,
-- `Convex.intrinsicClosure_ri_eq_intrinsicClosure hC`, then apply the finite-dimensional
-- owner-level bridge `supportFunction_ri_of_intrinsicClosure_eq`.
theorem supportFunction_intrinsicInterior {C : Set X} (hC : Convex 𝕜 C) :
    (δᵛ(· | ri[𝕜](C)) : Y → WithTopBot α) =
      (δᵛ(· | C) : Y → WithTopBot α) := by
  exact
    supportFunction_ri_of_intrinsicClosure_eq
      (C := C) hC.intrinsicClosure_ri_eq_intrinsicClosure

end Convex

end
