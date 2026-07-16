import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_0_3

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 : Type*}
variable {X : Type*}

local notation "P" => X × 𝕜

/-
Source/core/bridge triage:
- `source-facing`: Defn 12.1 classifies closed half-spaces in coordinates `(x, μ)` into three
  displayed forms: vertical, upper, and lower.
- `core/canonical`: the owner abstraction is Chapter 1's linear half-space owner on the product
  pairing layer `HasLinearPairing (X × 𝕜) (Y × 𝕜) 𝕜`.
- `bridge/view`: the three Chapter 12 textbook categories are derived predicates saying that a
  subset of `X × 𝕜` is one of those owner half-spaces with normals `(b, 0)` or `(b, -1)`.

Primitive data vs derived API:
- primitive data: the owner half-space constructors `closedHalfSpaceLE` and `closedHalfSpaceGE`
  at the product pairing layer;
- canonical Chapter 12 primitive bridge in this file: fixed-second-coordinate owner predicates for
  normals of the form `(b, η)`;
- derived API: the textbook predicates `vertical`, `upper`, `lower`, and their disjunction.
-/

section Coordinate

variable {Y : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing (X × 𝕜) (Y × 𝕜) 𝕜]

local notation "D" => Y × 𝕜

namespace Set

section

variable [LE 𝕜]

/-- A subset of `X × 𝕜` is a left-oriented fixed-second-coordinate closed half-space with
coefficient `η` when it is cut out by `⟪(x, μ), (b, η)⟫ₚ ≤ β` for some nontrivial induced
linear functional. -/
def IsCoordinateLEClosedHalfSpace (η : 𝕜) (s : Set P) : Prop :=
  ∃ b : Y, ∃ β : 𝕜,
    (HasLinearPairing.pairingLinear.flip ((b, η) : D) : P →ₗ[𝕜] 𝕜) ≠ 0 ∧
      s = closedHalfSpaceLE ((b, η) : D) β

/-- A subset of `X × 𝕜` is a right-oriented fixed-second-coordinate closed half-space with
coefficient `η` when it is cut out by `β ≤ ⟪(x, μ), (b, η)⟫ₚ` for some nontrivial induced
linear functional. -/
def IsCoordinateGEClosedHalfSpace (η : 𝕜) (s : Set P) : Prop :=
  ∃ b : Y, ∃ β : 𝕜,
    (HasLinearPairing.pairingLinear.flip ((b, η) : D) : P →ₗ[𝕜] 𝕜) ≠ 0 ∧
      s = closedHalfSpaceGE ((b, η) : D) β

/-- The owner half-space `closedHalfSpaceLE (b, η) β` has fixed-second-coordinate type `LE`
whenever the induced functional is nontrivial. -/
theorem isCoordinateLEClosedHalfSpace_closedHalfSpaceLE {η : 𝕜} {b : Y} {β : 𝕜}
    (hb : (HasLinearPairing.pairingLinear.flip ((b, η) : D) : P →ₗ[𝕜] 𝕜) ≠ 0) :
    IsCoordinateLEClosedHalfSpace (Y := Y) η (closedHalfSpaceLE ((b, η) : D) β : Set P) :=
  ⟨b, β, hb, rfl⟩

/-- The owner half-space `closedHalfSpaceGE (b, η) β` has fixed-second-coordinate type `GE`
whenever the induced functional is nontrivial. -/
theorem isCoordinateGEClosedHalfSpace_closedHalfSpaceGE {η : 𝕜} {b : Y} {β : 𝕜}
    (hb : (HasLinearPairing.pairingLinear.flip ((b, η) : D) : P →ₗ[𝕜] 𝕜) ≠ 0) :
    IsCoordinateGEClosedHalfSpace (Y := Y) η (closedHalfSpaceGE ((b, η) : D) β : Set P) :=
  ⟨b, β, hb, rfl⟩

/-- Every left-oriented fixed-second-coordinate closed half-space is a Chapter 1 closed
half-space. -/
theorem IsCoordinateLEClosedHalfSpace.isClosedHalfSpace {η : 𝕜} {s : Set P}
    (hs : IsCoordinateLEClosedHalfSpace (Y := Y) η s) :
    closedHalfSpace[D,𝕜] s := by
  rcases hs with ⟨b, β, hb, rfl⟩
  exact Set.closedHalfSpaceLE_isClosedHalfSpace hb

/-- Every right-oriented fixed-second-coordinate closed half-space is a Chapter 1 closed
half-space. -/
theorem IsCoordinateGEClosedHalfSpace.isClosedHalfSpace {η : 𝕜} {s : Set P}
    (hs : IsCoordinateGEClosedHalfSpace (Y := Y) η s) :
    closedHalfSpace[D,𝕜] s := by
  rcases hs with ⟨b, β, hb, rfl⟩
  exact Set.closedHalfSpaceGE_isClosedHalfSpace hb

end

section

variable [Preorder 𝕜]

/-- Every left-oriented fixed-second-coordinate closed half-space is an intrinsic
linear-functional closed half-space. -/
theorem IsCoordinateLEClosedHalfSpace.isClosedLinearHalfSpace {η : 𝕜} {s : Set P}
    (hs : IsCoordinateLEClosedHalfSpace (Y := Y) η s) :
    closedLinearHalfSpace[𝕜] s := by
  exact hs.isClosedHalfSpace.toClosedLinearHalfSpace

/-- Every right-oriented fixed-second-coordinate closed half-space is an intrinsic
linear-functional closed half-space. -/
theorem IsCoordinateGEClosedHalfSpace.isClosedLinearHalfSpace {η : 𝕜} {s : Set P}
    (hs : IsCoordinateGEClosedHalfSpace (Y := Y) η s) :
    closedLinearHalfSpace[𝕜] s := by
  exact hs.isClosedHalfSpace.toClosedLinearHalfSpace

end

end Set

end Coordinate

section Vertical

variable {Y : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing (X × 𝕜) (Y × 𝕜) 𝕜]

local notation "D" => Y × 𝕜

namespace Set

section

variable [LE 𝕜]

/-- A subset of `X × 𝕜` is vertical when it is cut out by an inequality
`⟪(x, μ), (b, 0)⟫ₚ ≤ β` with nontrivial induced linear functional. -/
abbrev IsVerticalClosedHalfSpace (s : Set P) : Prop :=
  IsCoordinateLEClosedHalfSpace (Y := Y) (0 : 𝕜) s

scoped[Rockafellar] notation3:max "verticalClosedHalfSpace[" Y "] " s =>
  Set.IsVerticalClosedHalfSpace (Y := Y) s

/-- The owner half-space `closedHalfSpaceLE (b, 0) β` is vertical whenever the induced
functional is nontrivial. -/
theorem isVerticalClosedHalfSpace_closedHalfSpaceLE {b : Y} {β : 𝕜}
    (hb : (HasLinearPairing.pairingLinear.flip ((b, (0 : 𝕜)) : D) : P →ₗ[𝕜] 𝕜) ≠ 0) :
    verticalClosedHalfSpace[Y] (closedHalfSpaceLE ((b, (0 : 𝕜)) : D) β : Set P) := by
  simpa [IsVerticalClosedHalfSpace] using
    (isCoordinateLEClosedHalfSpace_closedHalfSpaceLE (Y := Y) (η := (0 : 𝕜)) (b := b) (β := β)
      hb)

/-- Every vertical closed half-space is a closed half-space in the Chapter 1 owner sense. -/
theorem IsVerticalClosedHalfSpace.isClosedHalfSpace {s : Set P}
    (hs : verticalClosedHalfSpace[Y] s) : closedHalfSpace[D,𝕜] s := by
  simpa [IsVerticalClosedHalfSpace] using
    (IsCoordinateLEClosedHalfSpace.isClosedHalfSpace (Y := Y) (η := (0 : 𝕜)) hs)

end

section

variable [Preorder 𝕜]

/-- Every vertical closed half-space is an intrinsic linear-functional closed half-space. -/
theorem IsVerticalClosedHalfSpace.isClosedLinearHalfSpace {s : Set P}
    (hs : verticalClosedHalfSpace[Y] s) : closedLinearHalfSpace[𝕜] s := by
  exact hs.isClosedHalfSpace.toClosedLinearHalfSpace

end

end Set

end Vertical

section UpperLower

variable {Y : Type*}
variable [CommSemiring 𝕜] [Neg 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing (X × 𝕜) (Y × 𝕜) 𝕜]

local notation "D" => Y × 𝕜

namespace Set

section

variable [LE 𝕜]

/-- A subset of `X × 𝕜` is upper when it is the fixed-second-coordinate `LE` half-space
specialization with coefficient `-1`. -/
abbrev IsUpperClosedHalfSpace (s : Set P) : Prop :=
  IsCoordinateLEClosedHalfSpace (Y := Y) (-1 : 𝕜) s

/-- A subset of `X × 𝕜` is lower when it is the fixed-second-coordinate `GE` half-space
specialization with coefficient `-1`. -/
abbrev IsLowerClosedHalfSpace (s : Set P) : Prop :=
  IsCoordinateGEClosedHalfSpace (Y := Y) (-1 : 𝕜) s

/-- Defn 12.1 classification: every source-facing closed half-space type is vertical, upper,
or lower. -/
def IsVerticalUpperLowerClosedHalfSpace (s : Set P) : Prop :=
  IsVerticalClosedHalfSpace (Y := Y) s ∨
    IsUpperClosedHalfSpace (Y := Y) s ∨
      IsLowerClosedHalfSpace (Y := Y) s

-- The dual-side owner type cannot be inferred from `s : Set (X × 𝕜)` alone, so `Y`
-- remains explicit on these source-facing Chapter 12 notations.
scoped[Rockafellar] notation3:max "upperClosedHalfSpace[" Y "] " s =>
  Set.IsUpperClosedHalfSpace (Y := Y) s
scoped[Rockafellar] notation3:max "lowerClosedHalfSpace[" Y "] " s =>
  Set.IsLowerClosedHalfSpace (Y := Y) s
scoped[Rockafellar] notation3:max "verticalUpperLowerClosedHalfSpace[" Y "] " s =>
  Set.IsVerticalUpperLowerClosedHalfSpace (Y := Y) s

/-- The owner half-space `closedHalfSpaceLE (b, -1) β` is upper whenever the induced
functional is nontrivial. -/
theorem isUpperClosedHalfSpace_closedHalfSpaceLE {b : Y} {β : 𝕜}
    (hb : (HasLinearPairing.pairingLinear.flip ((b, (-1 : 𝕜)) : D) : P →ₗ[𝕜] 𝕜) ≠ 0) :
    upperClosedHalfSpace[Y] (closedHalfSpaceLE ((b, (-1 : 𝕜)) : D) β : Set P) := by
  simpa [IsUpperClosedHalfSpace] using
    (isCoordinateLEClosedHalfSpace_closedHalfSpaceLE (Y := Y) (η := (-1 : 𝕜)) (b := b) (β := β)
      hb)

/-- The source-facing bridge `closedHalfSpaceGE (b, -1) β` is lower whenever the induced
functional is nontrivial. -/
theorem isLowerClosedHalfSpace_closedHalfSpaceGE {b : Y} {β : 𝕜}
    (hb : (HasLinearPairing.pairingLinear.flip ((b, (-1 : 𝕜)) : D) : P →ₗ[𝕜] 𝕜) ≠ 0) :
    lowerClosedHalfSpace[Y] (closedHalfSpaceGE ((b, (-1 : 𝕜)) : D) β : Set P) := by
  simpa [IsLowerClosedHalfSpace] using
    (isCoordinateGEClosedHalfSpace_closedHalfSpaceGE (Y := Y) (η := (-1 : 𝕜)) (b := b) (β := β)
      hb)

/-- Every upper closed half-space is a closed half-space in the Chapter 1 owner sense. -/
theorem IsUpperClosedHalfSpace.isClosedHalfSpace {s : Set P}
    (hs : upperClosedHalfSpace[Y] s) : closedHalfSpace[D,𝕜] s := by
  simpa [IsUpperClosedHalfSpace] using
    (IsCoordinateLEClosedHalfSpace.isClosedHalfSpace (Y := Y) (η := (-1 : 𝕜)) hs)

/-- Every lower closed half-space is a closed half-space in the Chapter 1 owner sense. -/
theorem IsLowerClosedHalfSpace.isClosedHalfSpace {s : Set P}
    (hs : lowerClosedHalfSpace[Y] s) : closedHalfSpace[D,𝕜] s := by
  simpa [IsLowerClosedHalfSpace] using
    (IsCoordinateGEClosedHalfSpace.isClosedHalfSpace (Y := Y) (η := (-1 : 𝕜)) hs)

/-- Every Chapter 12 vertical/upper/lower closed half-space is a closed half-space. -/
theorem IsVerticalUpperLowerClosedHalfSpace.isClosedHalfSpace {s : Set P}
    (hs : verticalUpperLowerClosedHalfSpace[Y] s) :
    closedHalfSpace[D,𝕜] s := by
  rcases hs with hs | hs
  · exact hs.isClosedHalfSpace
  · rcases hs with hs | hs
    · exact hs.isClosedHalfSpace
    · exact hs.isClosedHalfSpace

end

section

variable [Preorder 𝕜]

/-- Every upper closed half-space is an intrinsic linear-functional closed half-space. -/
theorem IsUpperClosedHalfSpace.isClosedLinearHalfSpace {s : Set P}
    (hs : upperClosedHalfSpace[Y] s) : closedLinearHalfSpace[𝕜] s := by
  exact hs.isClosedHalfSpace.toClosedLinearHalfSpace

/-- Every lower closed half-space is an intrinsic linear-functional closed half-space. -/
theorem IsLowerClosedHalfSpace.isClosedLinearHalfSpace {s : Set P}
    (hs : lowerClosedHalfSpace[Y] s) : closedLinearHalfSpace[𝕜] s := by
  exact hs.isClosedHalfSpace.toClosedLinearHalfSpace

/-- Every Chapter 12 vertical/upper/lower closed half-space is an intrinsic
linear-functional closed half-space. -/
theorem IsVerticalUpperLowerClosedHalfSpace.isClosedLinearHalfSpace {s : Set P}
    (hs : verticalUpperLowerClosedHalfSpace[Y] s) : closedLinearHalfSpace[𝕜] s := by
  exact hs.isClosedHalfSpace.toClosedLinearHalfSpace

end

end Set

end UpperLower

end
