import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_2_0_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_9
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Proposition 2.5.16 says that a half-space whose defining level is `0`, i.e. a
  half-space through the origin, is a convex cone. The pairing-layer formulation here specializes
  to the textbook `R^n` statement.
- `core/canonical`: the source-facing owner layer for “through the origin” is intrinsic:
  homogeneous half-spaces are described by nonzero scalar-valued linear functionals at level `0`,
  via `Set.IsHomogeneousClosedHalfSpace` / `Set.IsHomogeneousOpenHalfSpace`, together with
  `Set.IsCone` and `Set.IsConvexCone`.
- `bridge/view`: the pairing-level half-space constructors `closedHalfSpaceLE`, `closedHalfSpaceGE`,
  `openHalfSpaceLT`, and `openHalfSpaceGT` are retained as bridge views into the intrinsic owner.
- Primitive data vs derived API: the primitive owner data are level-`0` linear-functional
  presentations; conic closure and convexity are theorem-level consequences.
- Domain-style sampling: this refinement reuses the chapter owners `closedHalfSpaceLE`,
  `closedHalfSpaceGE`, `openHalfSpaceLT`, and `openHalfSpaceGT`, the convexity theorems
  `closedHalfSpaceLE_convex`, `closedHalfSpaceGE_convex`, `openHalfSpaceLT_convex`, and
  `openHalfSpaceGT_convex`, and the source-facing cone owner `Set.IsCone`, now bundled through
  the homogeneous half-space owners.
- Layer target: `bridge/view`, specializing the chapter half-space owner layer to the homogeneous
  level `0` case appearing in Proposition 2.5.16.
-/

section HomogeneousClosedHalfSpaceOwner

variable {𝕜 : Type*} [Preorder 𝕜] [CommSemiring 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

namespace Set

/-- Source-facing homogeneous closed-half-space surface: level-`0` closed half-spaces in either
orientation. This is expressed directly through the established pairing-owner constructors. -/
abbrev IsHomogeneousClosedHalfSpace (Y : Type*) (𝕜 : Type*)
    [Preorder 𝕜] [CommSemiring 𝕜]
    {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]
    (s : Set X) : Prop :=
  ∃ b : Y, HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜) ∧
    (s = closedHalfSpaceLE b (0 : 𝕜) ∨ s = closedHalfSpaceGE b (0 : 𝕜))

scoped[Rockafellar] notation3:max "homClosedHalfSpace[" Y "," 𝕜 "] " s =>
  Set.IsHomogeneousClosedHalfSpace Y 𝕜 s

namespace IsHomogeneousClosedHalfSpace

/-- A homogeneous closed half-space is a closed half-space. -/
theorem isClosedHalfSpace {s : Set X}
    (hs : homClosedHalfSpace[Y,𝕜] s) :
    closedHalfSpace[Y,𝕜] s := by
  rcases hs with ⟨b, hb, rfl | rfl⟩
  · exact closedHalfSpaceLE_isClosedHalfSpace (Y := Y) (𝕜 := 𝕜) hb
  · exact closedHalfSpaceGE_isClosedHalfSpace (Y := Y) (𝕜 := 𝕜) hb

/-- Every homogeneous closed half-space is an intrinsic closed linear half-space. -/
theorem isClosedLinearHalfSpace {s : Set X}
    (hs : homClosedHalfSpace[Y,𝕜] s) :
    closedLinearHalfSpace[𝕜] s := by
  exact hs.isClosedHalfSpace.toClosedLinearHalfSpace

/-- The pairing-level left-oriented homogeneous closed half-space is homogeneous. -/
theorem closedHalfSpaceLE_zero (b : Y)
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    homClosedHalfSpace[Y,𝕜] (closedHalfSpaceLE b (0 : 𝕜) : Set X) := by
  exact ⟨b, hb, Or.inl rfl⟩

/-- The pairing-level right-oriented homogeneous closed half-space is homogeneous. -/
theorem closedHalfSpaceGE_zero (b : Y)
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    homClosedHalfSpace[Y,𝕜] (closedHalfSpaceGE b (0 : 𝕜) : Set X) := by
  exact ⟨b, hb, Or.inr rfl⟩

end IsHomogeneousClosedHalfSpace

end Set

end HomogeneousClosedHalfSpaceOwner

section HomogeneousOpenHalfSpaceOwner

variable {𝕜 : Type*} [Preorder 𝕜] [CommSemiring 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

namespace Set

/-- Source-facing homogeneous open-half-space surface: level-`0` open half-spaces in either
orientation. This is expressed directly through the established pairing-owner constructors. -/
abbrev IsHomogeneousOpenHalfSpace (Y : Type*) (𝕜 : Type*)
    [Preorder 𝕜] [CommSemiring 𝕜]
    {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]
    (s : Set X) : Prop :=
  ∃ b : Y, HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜) ∧
    (s = openHalfSpaceLT b (0 : 𝕜) ∨ s = openHalfSpaceGT b (0 : 𝕜))

scoped[Rockafellar] notation3:max "homOpenHalfSpace[" Y "," 𝕜 "] " s =>
  Set.IsHomogeneousOpenHalfSpace Y 𝕜 s

namespace IsHomogeneousOpenHalfSpace

/-- A homogeneous open half-space is an open half-space. -/
theorem isOpenHalfSpace {s : Set X}
    (hs : homOpenHalfSpace[Y,𝕜] s) :
    openHalfSpace[Y,𝕜] s := by
  rcases hs with ⟨b, hb, rfl | rfl⟩
  · exact openHalfSpaceLT_isOpenHalfSpace (Y := Y) (𝕜 := 𝕜) hb
  · exact openHalfSpaceGT_isOpenHalfSpace (Y := Y) (𝕜 := 𝕜) hb

/-- Every homogeneous open half-space is an intrinsic open linear half-space. -/
theorem isOpenLinearHalfSpace {s : Set X}
    (hs : homOpenHalfSpace[Y,𝕜] s) :
    openLinearHalfSpace[𝕜] s := by
  exact hs.isOpenHalfSpace.toOpenLinearHalfSpace

/-- The pairing-level left-oriented homogeneous open half-space is homogeneous. -/
theorem openHalfSpaceLT_zero (b : Y)
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    homOpenHalfSpace[Y,𝕜] (openHalfSpaceLT b (0 : 𝕜) : Set X) := by
  exact ⟨b, hb, Or.inl rfl⟩

/-- The pairing-level right-oriented homogeneous open half-space is homogeneous. -/
theorem openHalfSpaceGT_zero (b : Y)
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    homOpenHalfSpace[Y,𝕜] (openHalfSpaceGT b (0 : 𝕜) : Set X) := by
  exact ⟨b, hb, Or.inr rfl⟩

end IsHomogeneousOpenHalfSpace

end Set

end HomogeneousOpenHalfSpaceOwner

section ClosedCone

variable {𝕜 : Type*} [CommSemiring 𝕜] [Preorder 𝕜] [PosSMulMono 𝕜 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

namespace Set

/-- The homogeneous closed half-space `closedHalfSpaceLE b 0` is a cone. -/
theorem closedHalfSpaceLE_zero_isCone (b : Y) :
    Set.IsCone 𝕜 (closedHalfSpaceLE b (0 : 𝕜) : Set X) := by
  intro c hc x hx
  rw [mem_closedHalfSpaceLE_iff] at hx ⊢
  calc
    ⟪c • x, b⟫ₚ = c * ⟪x, b⟫ₚ := by simp
    _ ≤ c • (0 : 𝕜) := by
      simpa [smul_eq_mul] using smul_le_smul_of_nonneg_left hx hc.le
    _ = 0 := by simp

/-- The homogeneous closed half-space `closedHalfSpaceGE b 0` is a cone. -/
theorem closedHalfSpaceGE_zero_isCone (b : Y) :
    Set.IsCone 𝕜 (closedHalfSpaceGE b (0 : 𝕜) : Set X) := by
  intro c hc x hx
  rw [mem_closedHalfSpaceGE_iff] at hx ⊢
  calc
    (0 : 𝕜) = c • (0 : 𝕜) := by simp
    _ ≤ c • ⟪x, b⟫ₚ := by
      simpa using smul_le_smul_of_nonneg_left hx hc.le
    _ = ⟪c • x, b⟫ₚ := by simp

namespace IsHomogeneousClosedHalfSpace

/-- Every homogeneous closed half-space is a cone. -/
theorem isCone {s : Set X}
    (hs : homClosedHalfSpace[Y,𝕜] s) :
    Set.IsCone 𝕜 s := by
  rcases hs with ⟨b, _, rfl | rfl⟩
  · simpa using closedHalfSpaceLE_zero_isCone (X := X) (Y := Y) (𝕜 := 𝕜) b
  · simpa using closedHalfSpaceGE_zero_isCone (X := X) (Y := Y) (𝕜 := 𝕜) b

end IsHomogeneousClosedHalfSpace

end Set

end ClosedCone

section ClosedConvexCone

variable {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [PosSMulMono 𝕜 𝕜]
variable [IsOrderedAddMonoid 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

namespace Set

/-- Proposition 2.5.16, closed `≤` form: `closedHalfSpaceLE b 0` is a convex cone. -/
theorem closedHalfSpaceLE_zero_isConvexCone (b : Y) :
    Set.IsConvexCone 𝕜 (closedHalfSpaceLE b (0 : 𝕜) : Set X) := by
  exact ⟨closedHalfSpaceLE_zero_isCone b, closedHalfSpaceLE_convex b 0⟩

/-- Proposition 2.5.16, closed `≥` form: `closedHalfSpaceGE b 0` is a convex cone. -/
theorem closedHalfSpaceGE_zero_isConvexCone (b : Y) :
    Set.IsConvexCone 𝕜 (closedHalfSpaceGE b (0 : 𝕜) : Set X) := by
  exact ⟨closedHalfSpaceGE_zero_isCone b, closedHalfSpaceGE_convex b 0⟩

namespace IsHomogeneousClosedHalfSpace

/-- Proposition 2.5.16 in closed owner form: every homogeneous closed half-space is a convex
cone. -/
theorem isConvexCone {s : Set X}
    (hs : homClosedHalfSpace[Y,𝕜] s) :
    Set.IsConvexCone 𝕜 s := by
  exact ⟨isCone (Y := Y) hs, (isClosedLinearHalfSpace (Y := Y) hs).convex⟩

end IsHomogeneousClosedHalfSpace

end Set

end ClosedConvexCone

section OpenCone

variable {𝕜 : Type*} [CommSemiring 𝕜] [Preorder 𝕜] [PosSMulStrictMono 𝕜 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

namespace Set

/-- The homogeneous open half-space `openHalfSpaceLT b 0` is a cone. -/
theorem openHalfSpaceLT_zero_isCone (b : Y) :
    Set.IsCone 𝕜 (openHalfSpaceLT b (0 : 𝕜) : Set X) := by
  intro c hc x hx
  rw [mem_openHalfSpaceLT_iff] at hx ⊢
  calc
    ⟪c • x, b⟫ₚ = c • ⟪x, b⟫ₚ := by simp
    _ < c • (0 : 𝕜) := smul_lt_smul_of_pos_left hx hc
    _ = 0 := by simp

/-- The homogeneous open half-space `openHalfSpaceGT b 0` is a cone. -/
theorem openHalfSpaceGT_zero_isCone (b : Y) :
    Set.IsCone 𝕜 (openHalfSpaceGT b (0 : 𝕜) : Set X) := by
  intro c hc x hx
  rw [mem_openHalfSpaceGT_iff] at hx ⊢
  calc
    (0 : 𝕜) = c • (0 : 𝕜) := by simp
    _ < c • ⟪x, b⟫ₚ := by simpa using smul_lt_smul_of_pos_left hx hc
    _ = ⟪c • x, b⟫ₚ := by simp

namespace IsHomogeneousOpenHalfSpace

/-- Every homogeneous open half-space is a cone. -/
theorem isCone {s : Set X}
    (hs : homOpenHalfSpace[Y,𝕜] s) :
    Set.IsCone 𝕜 s := by
  rcases hs with ⟨b, _, rfl | rfl⟩
  · simpa using openHalfSpaceLT_zero_isCone (X := X) (Y := Y) (𝕜 := 𝕜) b
  · simpa using openHalfSpaceGT_zero_isCone (X := X) (Y := Y) (𝕜 := 𝕜) b

end IsHomogeneousOpenHalfSpace

end Set

end OpenCone

section OpenConvexCone

variable {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜]
variable [IsOrderedCancelAddMonoid 𝕜] [PosSMulStrictMono 𝕜 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

namespace Set

/-- Proposition 2.5.16, open `<` form: `openHalfSpaceLT b 0` is a convex cone. -/
theorem openHalfSpaceLT_zero_isConvexCone (b : Y) :
    Set.IsConvexCone 𝕜 (openHalfSpaceLT b (0 : 𝕜) : Set X) := by
  exact ⟨openHalfSpaceLT_zero_isCone b, openHalfSpaceLT_convex b 0⟩

/-- Proposition 2.5.16, open `>` form: `openHalfSpaceGT b 0` is a convex cone. -/
theorem openHalfSpaceGT_zero_isConvexCone (b : Y) :
    Set.IsConvexCone 𝕜 (openHalfSpaceGT b (0 : 𝕜) : Set X) := by
  exact ⟨openHalfSpaceGT_zero_isCone b, openHalfSpaceGT_convex b 0⟩

namespace IsHomogeneousOpenHalfSpace

/-- Proposition 2.5.16 in open owner form: every homogeneous open half-space is a convex cone. -/
theorem isConvexCone {s : Set X}
    (hs : homOpenHalfSpace[Y,𝕜] s) :
    Set.IsConvexCone 𝕜 s := by
  exact ⟨isCone (Y := Y) hs, (isOpenLinearHalfSpace (Y := Y) hs).convex⟩

end IsHomogeneousOpenHalfSpace

end Set

end OpenConvexCone
