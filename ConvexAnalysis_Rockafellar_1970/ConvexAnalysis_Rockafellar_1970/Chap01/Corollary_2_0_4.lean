import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_0_3
import Mathlib.Analysis.Convex.Basic

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Corollary 2.0.4 says that each of the four oriented half-spaces cut out by one
  pairing inequality is convex; the coordinate-free formulation here specializes to the textbook
  `ℝ^n` statement.
- `core/canonical`: the owner abstraction is `Convex 𝕜 s`; the canonical mathlib theorems are
  `convex_halfSpace_le`, `convex_halfSpace_ge`, `convex_halfSpace_lt`, and
  `convex_halfSpace_gt`, applied to the linear functional `x ↦ ⟪x, b⟫ₚ`.
- `bridge/view`: the chapter owner predicates `IsClosedHalfSpace` and `IsOpenHalfSpace` from
  Definition 2.0.3 package the textbook half-space presentations, while the owner subsets
  `closedHalfSpaceLE`, `closedHalfSpaceGE`, `openHalfSpaceLT`, and `openHalfSpaceGT` realize the
  four oriented textbook inequalities directly.
- Primitive data vs derived API: the actual half-space subsets are primitive data; convexity and
  closedness are derived theorem-level API. The primitive bridge theorems below are stated first
  with local linearity/continuity assumptions, then specialized to the chapter typeclass owners.
- Domain-style sampling:
  `closedHalfSpaceLE`/`openHalfSpaceLT` and `IsClosedHalfSpace`/`IsOpenHalfSpace` from
  `Definition_2_0_3`, and the mathlib owner theorems `convex_halfSpace_le`,
  `convex_halfSpace_ge`, `convex_halfSpace_lt`, and `convex_halfSpace_gt`.
-/

section

open scoped Rockafellar

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
variable [Module 𝕜 R] [PosSMulMono 𝕜 R]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [HasPairing X Y R]

/-- The left-oriented closed half-space is convex once the cutting pairing functional is linear. -/
theorem closedHalfSpaceLE_convex_of_isLinear (b : Y) (β : R)
    (hb : IsLinearMap 𝕜 (fun x : X ↦ (⟪x, b⟫ₚ : R))) :
    Convex 𝕜 (closedHalfSpaceLE b β : Set X) := by
  simpa [closedHalfSpaceLE] using convex_halfSpace_le hb β

/-- The right-oriented closed half-space is convex once the cutting pairing functional is linear. -/
theorem closedHalfSpaceGE_convex_of_isLinear (b : Y) (β : R)
    (hb : IsLinearMap 𝕜 (fun x : X ↦ (⟪x, b⟫ₚ : R))) :
    Convex 𝕜 (closedHalfSpaceGE b β : Set X) := by
  simpa [closedHalfSpaceGE] using convex_halfSpace_ge hb β

namespace Set

/-- A set presented as one oriented closed pairing half-space is convex when its cutting pairing
evaluation `x ↦ ⟪x, b⟫ₚ` is linear in `x`. -/
theorem convex_of_exists_eq_closedHalfSpace_of_forall_isLinear {s : Set X}
    (hs : ∃ b : Y, ∃ β : R,
      (s = closedHalfSpaceLE b β ∨ s = closedHalfSpaceGE b β) ∧
      IsLinearMap 𝕜 (fun x : X ↦ (⟪x, b⟫ₚ : R))) :
    Convex 𝕜 s := by
  rcases hs with ⟨b, β, hs, hlin⟩
  rcases hs with rfl | rfl
  · exact closedHalfSpaceLE_convex_of_isLinear b β hlin
  · exact closedHalfSpaceGE_convex_of_isLinear b β hlin

end Set

end

section

open scoped Rockafellar

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [PosSMulMono 𝕜 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]

/-- Every intrinsic closed linear half-space is convex. -/
theorem Set.IsClosedLinearHalfSpace.convex {s : Set X}
    (hs : closedLinearHalfSpace[𝕜] s) :
    Convex 𝕜 s := by
  rcases hs with ⟨f, β, -, rfl | rfl⟩
  · simpa using (convex_halfSpace_le f.isLinear β)
  · simpa using (convex_halfSpace_ge f.isLinear β)

end

section

open scoped Rockafellar

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedCancelAddMonoid 𝕜]
variable [PosSMulStrictMono 𝕜 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]

/-- Every intrinsic open linear half-space is convex. -/
theorem Set.IsOpenLinearHalfSpace.convex {s : Set X}
    (hs : openLinearHalfSpace[𝕜] s) :
    Convex 𝕜 s := by
  rcases hs with ⟨f, β, -, rfl | rfl⟩
  · simpa using (convex_halfSpace_lt f.isLinear β)
  · simpa using (convex_halfSpace_gt f.isLinear β)

/-- Every intrinsic linear half-space (closed or open orientation) is convex. -/
theorem Set.IsLinearHalfSpace.convex {s : Set X}
    (hs : linearHalfSpace[𝕜] s) :
    Convex 𝕜 s := by
  rcases hs with hs | hs
  · exact Set.IsClosedLinearHalfSpace.convex hs
  · exact Set.IsOpenLinearHalfSpace.convex hs

end

section

open scoped Rockafellar

variable {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [PosSMulMono 𝕜 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- The left-oriented closed half-space `closedHalfSpaceLE b β` is convex. -/
theorem closedHalfSpaceLE_convex (b : Y) (β : 𝕜) :
    Convex 𝕜 (closedHalfSpaceLE b β : Set X) := by
  exact
    closedHalfSpaceLE_convex_of_isLinear b β
      (HasLinearPairing.isLinear_pairing_left b)

/-- The right-oriented closed half-space `closedHalfSpaceGE b β` is convex. -/
theorem closedHalfSpaceGE_convex (b : Y) (β : 𝕜) :
    Convex 𝕜 (closedHalfSpaceGE b β : Set X) := by
  exact
    closedHalfSpaceGE_convex_of_isLinear b β
      (HasLinearPairing.isLinear_pairing_left b)

/-- Every closed half-space is convex. -/
theorem Set.IsClosedHalfSpace.convex {s : Set X}
    (hs : closedHalfSpace[Y,𝕜] s) :
    Convex 𝕜 s := by
  exact Set.IsClosedLinearHalfSpace.convex hs.toClosedLinearHalfSpace

end

section

open scoped Rockafellar

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedCancelAddMonoid R]
variable [Module 𝕜 R] [PosSMulStrictMono 𝕜 R]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [HasPairing X Y R]

/-- The left-oriented open half-space is convex once the cutting pairing functional is linear. -/
theorem openHalfSpaceLT_convex_of_isLinear (b : Y) (β : R)
    (hb : IsLinearMap 𝕜 (fun x : X ↦ (⟪x, b⟫ₚ : R))) :
    Convex 𝕜 (openHalfSpaceLT b β : Set X) := by
  simpa [openHalfSpaceLT] using convex_halfSpace_lt hb β

/-- The right-oriented open half-space is convex once the cutting pairing functional is linear. -/
theorem openHalfSpaceGT_convex_of_isLinear (b : Y) (β : R)
    (hb : IsLinearMap 𝕜 (fun x : X ↦ (⟪x, b⟫ₚ : R))) :
    Convex 𝕜 (openHalfSpaceGT b β : Set X) := by
  simpa [openHalfSpaceGT] using convex_halfSpace_gt hb β

namespace Set

/-- A set presented as one oriented open pairing half-space is convex when its cutting pairing
evaluation `x ↦ ⟪x, b⟫ₚ` is linear in `x`. -/
theorem convex_of_exists_eq_openHalfSpace_of_forall_isLinear {s : Set X}
    (hs : ∃ b : Y, ∃ β : R,
      (s = openHalfSpaceLT b β ∨ s = openHalfSpaceGT b β) ∧
      IsLinearMap 𝕜 (fun x : X ↦ (⟪x, b⟫ₚ : R))) :
    Convex 𝕜 s := by
  rcases hs with ⟨b, β, hs, hlin⟩
  rcases hs with rfl | rfl
  · exact openHalfSpaceLT_convex_of_isLinear b β hlin
  · exact openHalfSpaceGT_convex_of_isLinear b β hlin

end Set

end

section

open scoped Rockafellar

variable {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsOrderedCancelAddMonoid 𝕜]
variable [PosSMulStrictMono 𝕜 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- The left-oriented open half-space `openHalfSpaceLT b β` is convex. -/
theorem openHalfSpaceLT_convex (b : Y) (β : 𝕜) :
    Convex 𝕜 (openHalfSpaceLT b β : Set X) := by
  exact
    openHalfSpaceLT_convex_of_isLinear b β
      (HasLinearPairing.isLinear_pairing_left b)

/-- The right-oriented open half-space `openHalfSpaceGT b β` is convex. -/
theorem openHalfSpaceGT_convex (b : Y) (β : 𝕜) :
    Convex 𝕜 (openHalfSpaceGT b β : Set X) := by
  exact
    openHalfSpaceGT_convex_of_isLinear b β
      (HasLinearPairing.isLinear_pairing_left b)

/-- Every open half-space is convex. -/
theorem Set.IsOpenHalfSpace.convex {s : Set X}
    (hs : openHalfSpace[Y,𝕜] s) :
    Convex 𝕜 s := by
  exact Set.IsOpenLinearHalfSpace.convex hs.toOpenLinearHalfSpace

/-- Corollary 2.0.4: every textbook half-space, whether closed or open, is convex. -/
theorem Set.IsHalfSpace.convex {s : Set X}
    (hs : halfSpace[Y,𝕜] s) :
    Convex 𝕜 s := by
  exact Set.IsLinearHalfSpace.convex hs.toLinearHalfSpace

end

section

open scoped Rockafellar

variable {R : Type*} [Preorder R]
variable [TopologicalSpace R] [OrderClosedTopology R]
variable {X : Type*} [TopologicalSpace X]
variable {Y : Type*} [HasPairing X Y R]

/-- The left-oriented closed half-space is closed once `x ↦ ⟪x, b⟫ₚ` is continuous. -/
theorem closedHalfSpaceLE_closed_of_continuous (b : Y) (β : R)
    (hb : Continuous (fun x : X ↦ (⟪x, b⟫ₚ : R))) :
    IsClosed (closedHalfSpaceLE b β : Set X) := by
  simpa [closedHalfSpaceLE] using isClosed_le hb continuous_const

/-- The right-oriented closed half-space is closed once `x ↦ ⟪x, b⟫ₚ` is continuous. -/
theorem closedHalfSpaceGE_closed_of_continuous (b : Y) (β : R)
    (hb : Continuous (fun x : X ↦ (⟪x, b⟫ₚ : R))) :
    IsClosed (closedHalfSpaceGE b β : Set X) := by
  simpa [closedHalfSpaceGE] using isClosed_le continuous_const hb

namespace Set

/-- A set presented as one oriented closed pairing half-space is closed when its cutting pairing
evaluation `x ↦ ⟪x, b⟫ₚ` is continuous in `x`. -/
theorem isClosed_of_exists_eq_closedHalfSpace_of_forall_continuous {s : Set X}
    (hs : ∃ b : Y, ∃ β : R,
      (s = closedHalfSpaceLE b β ∨ s = closedHalfSpaceGE b β) ∧
      Continuous (fun x : X ↦ (⟪x, b⟫ₚ : R))) :
    IsClosed s := by
  rcases hs with ⟨b, β, hs, hcont⟩
  rcases hs with rfl | rfl
  · exact closedHalfSpaceLE_closed_of_continuous b β hcont
  · exact closedHalfSpaceGE_closed_of_continuous b β hcont

end Set

section

variable [HasContinuousPairing X Y R]

/-- The left-oriented closed half-space `closedHalfSpaceLE b β` is closed. -/
theorem closedHalfSpaceLE_closed (b : Y) (β : R) :
    IsClosed (closedHalfSpaceLE b β : Set X) := by
  exact closedHalfSpaceLE_closed_of_continuous b β
    (HasContinuousPairing.continuous_pairing_left b)

/-- The right-oriented closed half-space `closedHalfSpaceGE b β` is closed. -/
theorem closedHalfSpaceGE_closed (b : Y) (β : R) :
    IsClosed (closedHalfSpaceGE b β : Set X) := by
  exact closedHalfSpaceGE_closed_of_continuous b β
    (HasContinuousPairing.continuous_pairing_left b)

end

end

section

open scoped Rockafellar

variable {𝕜 : Type*} [CommSemiring 𝕜] [Preorder 𝕜]
variable [TopologicalSpace 𝕜] [OrderClosedTopology 𝕜]
variable {X : Type*} [TopologicalSpace X] [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- Every closed half-space is closed when each nontrivial pairing evaluation is continuous. -/
theorem Set.IsClosedHalfSpace.isClosed_of_forall_continuous {s : Set X}
    (hs : closedHalfSpace[Y,𝕜] s)
    (hcont : ∀ b : Y,
      HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜) →
        Continuous (fun x : X ↦ (⟪x, b⟫ₚ : 𝕜))) :
    IsClosed s := by
  rcases hs with ⟨b, β, hb, hs | hs⟩
  · rcases hs with rfl
    exact closedHalfSpaceLE_closed_of_continuous b β (hcont b hb)
  · rcases hs with rfl
    exact closedHalfSpaceGE_closed_of_continuous b β (hcont b hb)

section

variable [HasContinuousPairing X Y 𝕜]

/-- Every closed half-space is closed. -/
theorem Set.IsClosedHalfSpace.isClosed {s : Set X}
    (hs : closedHalfSpace[Y,𝕜] s) :
    IsClosed s := by
  exact Set.IsClosedHalfSpace.isClosed_of_forall_continuous hs
    (fun b _ ↦ HasContinuousPairing.continuous_pairing_left b)

end

end
