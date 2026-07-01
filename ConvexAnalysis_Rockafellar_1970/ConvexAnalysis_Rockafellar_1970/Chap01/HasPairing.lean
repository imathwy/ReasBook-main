import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Data.EReal.Basic
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib
universe u v w

/-- Primitive pairing data for Fenchel-style constructions and support-function constructions. -/
class HasPairing (X : Type u) (Y : Type v) (L : Type w) where
  pairing : X → Y → L

scoped[Rockafellar] notation "⟪" x ", " y "⟫ₚ" => HasPairing.pairing x y

open scoped Rockafellar

/-- Primitive bilinear pairing data for dual-cone, normal-cone, and separation constructions. The
field is stored in curried linear form so that downstream declarations can use the linear structure
directly rather than recovering it from a weaker raw pairing. -/
class HasLinearPairing (X : Type u) (Y : Type v) (𝕜 : Type w)
    [CommSemiring 𝕜]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y] where
  pairingLinear : X →ₗ[𝕜] Module.Dual 𝕜 Y

namespace HasLinearPairing

/-- Nondegeneracy owner for a linear pairing: the left linearization is injective. -/
class Nondegenerate (X : Type u) (Y : Type v) (𝕜 : Type w)
    [CommSemiring 𝕜]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    [HasLinearPairing X Y 𝕜] : Prop where
  injective_pairingLinear :
    Function.Injective (HasLinearPairing.pairingLinear : X →ₗ[𝕜] Module.Dual 𝕜 Y)

section

variable {𝕜 : Type w} {X : Type u} {Y : Type v}
variable [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] [Nondegenerate X Y 𝕜]

/-- Projection theorem for the canonical pairing-nondegeneracy owner. -/
theorem injective_pairingLinear :
    Function.Injective (HasLinearPairing.pairingLinear : X →ₗ[𝕜] Module.Dual 𝕜 Y) :=
  Nondegenerate.injective_pairingLinear

end

end HasLinearPairing

/-- Continuity layer for the left evaluation maps of a pairing: for each `y`, the scalar-valued
map `x ↦ ⟪x, y⟫ₚ` is continuous. This is the minimal topological owner needed for closed-half-space
preimage results. -/
class HasContinuousPairing (X : Type u) (Y : Type v) (𝕜 : Type w)
    [TopologicalSpace X] [TopologicalSpace 𝕜] [HasPairing X Y 𝕜] : Prop where
  continuous_pairing_left : ∀ y : Y, Continuous (fun x : X ↦ (⟪x, y⟫ₚ : 𝕜))

/-- Compatibility layer for two oriented pairings on `(X, Y)` and `(Y, X)`. This owner records
the swap identity needed when support-function APIs use the opposite pairing orientation from
hyperplane-separation APIs. -/
class HasPairingSwap (X : Type u) (Y : Type v) (𝕜 : Type w)
    [HasPairing X Y 𝕜] [HasPairing Y X 𝕜] : Prop where
  pairing_swap : ∀ x : X, ∀ y : Y, (⟪x, y⟫ₚ : 𝕜) = ⟪y, x⟫ₚ

/-- Compatibility layer for oriented pairings with right negation. This owner records the identity
`⟪x, -y⟫ = -⟪x, y⟫` used repeatedly by concave/convex conjugacy sign-duality bridges. -/
class HasPairingNegRight (X : Type u) (Y : Type v) (𝕜 : Type w)
    [Neg Y] [Neg 𝕜] [HasPairing X Y 𝕜] : Prop where
  pairing_neg_right : ∀ x : X, ∀ y : Y, (⟪x, -y⟫ₚ : 𝕜) = -⟪x, y⟫ₚ

/-- Compatibility layer for oriented pairings with left negation. This owner records the identity
`⟪-x, y⟫ = -⟪x, y⟫` used by support-function infimum/supremum sign-duality bridges. -/
class HasPairingNegLeft (X : Type u) (Y : Type v) (𝕜 : Type w)
    [Neg X] [Neg 𝕜] [HasPairing X Y 𝕜] : Prop where
  pairing_neg_left : ∀ x : X, ∀ y : Y, (⟪-x, y⟫ₚ : 𝕜) = -⟪x, y⟫ₚ

/-- Compatibility layer for oriented pairings with right addition. This owner records the identity
`⟪x, y₁ + y₂⟫ = ⟪x, y₁⟫ + ⟪x, y₂⟫` used by translation formulas for conjugates and support terms. -/
class HasPairingAddRight (X : Type u) (Y : Type v) (𝕜 : Type w)
    [Add Y] [Add 𝕜] [HasPairing X Y 𝕜] : Prop where
  pairing_add_right : ∀ x : X, ∀ y₁ y₂ : Y, (⟪x, y₁ + y₂⟫ₚ : 𝕜) = ⟪x, y₁⟫ₚ + ⟪x, y₂⟫ₚ

/-- Compatibility layer for oriented pairings with right scalar multiplication. This owner records
the identity `⟪x, c • y⟫ = c * ⟪x, y⟫`, used by cone and positive-homogeneity bridges. -/
class HasPairingSMulRight (X : Type u) (Y : Type v) (𝕜 : Type w)
    [SMul 𝕜 Y] [Mul 𝕜] [HasPairing X Y 𝕜] : Prop where
  pairing_smul_right : ∀ x : X, ∀ c : 𝕜, ∀ y : Y, (⟪x, c • y⟫ₚ : 𝕜) = c * ⟪x, y⟫ₚ

/-- Compatibility layer for oriented pairings with left addition. This owner records the identity
`⟪x₁ + x₂, y⟫ = ⟪x₁, y⟫ + ⟪x₂, y⟫` used by finite-decomposition formulas for infimal
convolution and conjugacy. -/
class HasPairingAddLeft (X : Type u) (Y : Type v) (𝕜 : Type w)
    [Add X] [Add 𝕜] [HasPairing X Y 𝕜] : Prop where
  pairing_add_left :
    ∀ x₁ x₂ : X, ∀ y : Y, (⟪x₁ + x₂, y⟫ₚ : 𝕜) = ⟪x₁, y⟫ₚ + ⟪x₂, y⟫ₚ

/-- Compatibility layer for oriented pairings with right subtraction. This owner records the
identity `⟪x, y₁ - y₀⟫ = ⟪x, y₁⟫ - ⟪x, y₀⟫`, used by cyclic-to-monotone bridges and
subgradient-difference estimates. -/
class HasPairingSubRight (X : Type u) (Y : Type v) (𝕜 : Type w)
    [Sub Y] [Sub 𝕜] [HasPairing X Y 𝕜] : Prop where
  pairing_sub_right : ∀ x : X, ∀ y₁ y₀ : Y, (⟪x, y₁ - y₀⟫ₚ : 𝕜) = ⟪x, y₁⟫ₚ - ⟪x, y₀⟫ₚ

/-- Compatibility layer for oriented pairings with left subtraction. This owner records the
identity `⟪x₁ - x₀, y⟫ = ⟪x₁, y⟫ - ⟪x₀, y⟫`, used by cyclic-to-monotone bridges and
subgradient-difference estimates. -/
class HasPairingSubLeft (X : Type u) (Y : Type v) (𝕜 : Type w)
    [Sub X] [Sub 𝕜] [HasPairing X Y 𝕜] : Prop where
  pairing_sub_left : ∀ x₁ x₀ : X, ∀ y : Y, (⟪x₁ - x₀, y⟫ₚ : 𝕜) = ⟪x₁, y⟫ₚ - ⟪x₀, y⟫ₚ

/-- Compatibility layer for oriented pairings with a distinguished right zero element. This owner
records the identity `⟪x, 0⟫ = 0`, used by zero-subgradient characterizations on pairing-level
surfaces. -/
class HasPairingZeroRight (X : Type u) (Y : Type v) (𝕜 : Type w)
    [Zero Y] [Zero 𝕜] [HasPairing X Y 𝕜] : Prop where
  pairing_zero_right : ∀ x : X, (⟪x, (0 : Y)⟫ₚ : 𝕜) = 0

/-- Compatibility layer for oriented pairings with a distinguished left zero element. This owner
records the identity `⟪0, y⟫ = 0`, used by zero-basepoint conjugacy and saddle-value formulas. -/
class HasPairingZeroLeft (X : Type u) (Y : Type v) (𝕜 : Type w)
    [Zero X] [Zero 𝕜] [HasPairing X Y 𝕜] : Prop where
  pairing_zero_left : ∀ y : Y, (⟪(0 : X), y⟫ₚ : 𝕜) = 0

section PairingSMulRight

variable {X : Type u} {Y : Type v} {𝕜 : Type w}
variable [SMul 𝕜 Y] [Mul 𝕜] [HasPairing X Y 𝕜] [HasPairingSMulRight X Y 𝕜]

@[simp] theorem pairing_smul_right (x : X) (c : 𝕜) (y : Y) :
    (⟪x, c • y⟫ₚ : 𝕜) = c * ⟪x, y⟫ₚ :=
  HasPairingSMulRight.pairing_smul_right x c y

end PairingSMulRight

section PairingZeroRight

variable {X : Type u} {Y : Type v} {𝕜 : Type w}
variable [Zero Y] [Zero 𝕜] [HasPairing X Y 𝕜] [HasPairingZeroRight X Y 𝕜]

@[simp] theorem pairing_zero_right (x : X) : (⟪x, (0 : Y)⟫ₚ : 𝕜) = 0 :=
  HasPairingZeroRight.pairing_zero_right x

end PairingZeroRight

section PairingZeroLeft

variable {X : Type u} {Y : Type v} {𝕜 : Type w}
variable [Zero X] [Zero 𝕜] [HasPairing X Y 𝕜] [HasPairingZeroLeft X Y 𝕜]

@[simp] theorem pairing_zero_left (y : Y) : (⟪(0 : X), y⟫ₚ : 𝕜) = 0 :=
  HasPairingZeroLeft.pairing_zero_left y

end PairingZeroLeft

namespace HasPairing

section Swap

variable {X : Type u} {Y : Type v} {L : Type w}

/-- The canonical swapped view of a pairing, used when a construction reads the same pairing in
the opposite orientation. This is a bridge/view owner, not a second primitive pairing notion. -/
@[reducible] def swap [HasPairing X Y L] : HasPairing Y X L where
  pairing y x := ⟪x, y⟫ₚ

@[simp] theorem swap_pairing [HasPairing X Y L] (y : Y) (x : X) :
    @HasPairing.pairing Y X L (swap (X := X) (Y := Y) (L := L)) y x = ⟪x, y⟫ₚ :=
  rfl

end Swap

end HasPairing

section LinearToRaw

variable {𝕜 : Type w} {X : Type u} {Y : Type v}
variable [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]

instance instHasPairingOfHasLinearPairing [HasLinearPairing X Y 𝕜] : HasPairing X Y 𝕜 where
  pairing x y := (HasLinearPairing.pairingLinear x) y

end LinearToRaw

namespace HasLinearPairing

section

variable {𝕜 : Type w} {X : Type u} {Y : Type v}
variable [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

@[simp] theorem pairing_eq_pairingLinear (x : X) (y : Y) :
    (HasPairing.pairing x y : 𝕜) = (HasLinearPairing.pairingLinear x) y :=
  rfl

/-- In a linear pairing layer, each left evaluation map `x ↦ ⟪x, b⟫ₚ` is linear. This is the
canonical short bridge from pairing owners to `IsLinearMap`-based convexity APIs. -/
theorem isLinear_pairing_left (b : Y) :
    IsLinearMap 𝕜 (fun x : X ↦ (⟪x, b⟫ₚ : 𝕜)) := by
  simpa using (HasLinearPairing.pairingLinear.flip b).isLinear

end

end HasLinearPairing

section LinearNegRight

variable {𝕜 : Type w} {X : Type u} {Y : Type v}
variable [CommRing 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommGroup Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- Any linear pairing is automatically compatible with right negation in the second argument. -/
instance instHasPairingNegRightOfHasLinearPairing : HasPairingNegRight X Y 𝕜 where
  pairing_neg_right x y := by
    change (HasLinearPairing.pairingLinear x) (-y) = -((HasLinearPairing.pairingLinear x) y)
    rw [(neg_one_smul 𝕜 y).symm]
    rw [LinearMap.map_smul]
    simp

end LinearNegRight

section SwapCompat

variable {𝕜 : Type w} {X : Type u} {Y : Type v}
variable [HasPairing X Y 𝕜] [HasPairing Y X 𝕜]

/-- Swap compatibility is symmetric between the two orientations. -/
instance instHasPairingSwapSymm [HasPairingSwap X Y 𝕜] : HasPairingSwap Y X 𝕜 where
  pairing_swap y x := (HasPairingSwap.pairing_swap x y).symm

end SwapCompat

section SwapNegLeft

variable {𝕜 : Type w} {X : Type u} {Y : Type v}
variable [Neg X] [Neg 𝕜]
variable [HasPairing X Y 𝕜] [HasPairing Y X 𝕜]
variable [HasPairingSwap X Y 𝕜] [HasPairingNegRight Y X 𝕜]

/-- Left-negation compatibility is obtained from swap compatibility plus right-negation
compatibility on the swapped orientation. -/
instance instHasPairingNegLeftOfSwapNegRight : HasPairingNegLeft X Y 𝕜 where
  pairing_neg_left x y := by
    calc
      (⟪-x, y⟫ₚ : 𝕜) = ⟪y, -x⟫ₚ := HasPairingSwap.pairing_swap (-x) y
      _ = -⟪y, x⟫ₚ := HasPairingNegRight.pairing_neg_right y x
      _ = -⟪x, y⟫ₚ := by rw [HasPairingSwap.pairing_swap x y]

end SwapNegLeft

section SubFromAddNeg

variable {𝕜 : Type w} {X : Type u} {Y : Type v}
variable [AddGroup X] [AddGroup Y] [AddGroup 𝕜]
variable [HasPairing X Y 𝕜]
variable [HasPairingAddRight X Y 𝕜] [HasPairingAddLeft X Y 𝕜]
variable [HasPairingNegRight X Y 𝕜] [HasPairingNegLeft X Y 𝕜]

/-- Right-subtraction compatibility follows from right-addition and right-negation compatibility. -/
instance instHasPairingSubRightOfAddNeg : HasPairingSubRight X Y 𝕜 where
  pairing_sub_right x y₁ y₀ := by
    calc
      (⟪x, y₁ - y₀⟫ₚ : 𝕜)
          = (⟪x, y₁ + (-y₀)⟫ₚ : 𝕜) := by rw [sub_eq_add_neg]
      _ = ⟪x, y₁⟫ₚ + ⟪x, -y₀⟫ₚ := HasPairingAddRight.pairing_add_right x y₁ (-y₀)
      _ = ⟪x, y₁⟫ₚ + (-⟪x, y₀⟫ₚ) := by rw [HasPairingNegRight.pairing_neg_right x y₀]
      _ = ⟪x, y₁⟫ₚ - ⟪x, y₀⟫ₚ := by rw [sub_eq_add_neg]

/-- Left-subtraction compatibility follows from left-addition and left-negation compatibility. -/
instance instHasPairingSubLeftOfAddNeg : HasPairingSubLeft X Y 𝕜 where
  pairing_sub_left x₁ x₀ y := by
    calc
      (⟪x₁ - x₀, y⟫ₚ : 𝕜)
          = (⟪x₁ + (-x₀), y⟫ₚ : 𝕜) := by rw [sub_eq_add_neg]
      _ = ⟪x₁, y⟫ₚ + ⟪-x₀, y⟫ₚ := HasPairingAddLeft.pairing_add_left x₁ (-x₀) y
      _ = ⟪x₁, y⟫ₚ + (-⟪x₀, y⟫ₚ) := by rw [HasPairingNegLeft.pairing_neg_left x₀ y]
      _ = ⟪x₁, y⟫ₚ - ⟪x₀, y⟫ₚ := by rw [sub_eq_add_neg]

end SubFromAddNeg

section LinearAddRight

variable {𝕜 : Type w} {X : Type u} {Y : Type v}
variable [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- Any linear pairing is automatically compatible with right addition in the second argument. -/
instance instHasPairingAddRightOfHasLinearPairing : HasPairingAddRight X Y 𝕜 where
  pairing_add_right x y₁ y₂ := by
    change (HasLinearPairing.pairingLinear x) (y₁ + y₂) =
      (HasLinearPairing.pairingLinear x) y₁ + (HasLinearPairing.pairingLinear x) y₂
    exact LinearMap.map_add (HasLinearPairing.pairingLinear x) y₁ y₂

end LinearAddRight

section LinearSMulRight

variable {𝕜 : Type w} {X : Type u} {Y : Type v}
variable [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- Any linear pairing is automatically compatible with right scalar multiplication in the second
argument. -/
instance instHasPairingSMulRightOfHasLinearPairing : HasPairingSMulRight X Y 𝕜 where
  pairing_smul_right x c y := by
    change (HasLinearPairing.pairingLinear x) (c • y) =
      c * ((HasLinearPairing.pairingLinear x) y)
    rw [map_smul, smul_eq_mul]

end LinearSMulRight

section LinearAddLeft

variable {𝕜 : Type w} {X : Type u} {Y : Type v}
variable [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- Any linear pairing is automatically compatible with left addition in the first argument. -/
instance instHasPairingAddLeftOfHasLinearPairing : HasPairingAddLeft X Y 𝕜 where
  pairing_add_left x₁ x₂ y := by
    change (HasLinearPairing.pairingLinear (x₁ + x₂)) y =
      (HasLinearPairing.pairingLinear x₁) y + (HasLinearPairing.pairingLinear x₂) y
    exact congrArg (fun g : Module.Dual 𝕜 Y => g y)
      (LinearMap.map_add
        (HasLinearPairing.pairingLinear : X →ₗ[𝕜] Module.Dual 𝕜 Y) x₁ x₂)

end LinearAddLeft

section LinearSub

variable {𝕜 : Type w} {X : Type u} {Y : Type v}
variable [CommRing 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- Any linear pairing is automatically compatible with right subtraction in the second argument. -/
instance instHasPairingSubRightOfHasLinearPairing : HasPairingSubRight X Y 𝕜 where
  pairing_sub_right x y₁ y₀ := by
    change (HasLinearPairing.pairingLinear x) (y₁ - y₀) =
      (HasLinearPairing.pairingLinear x) y₁ - (HasLinearPairing.pairingLinear x) y₀
    exact (HasLinearPairing.pairingLinear (X := X) (Y := Y) (𝕜 := 𝕜) x).map_sub y₁ y₀

/-- Any linear pairing is automatically compatible with left subtraction in the first argument. -/
instance instHasPairingSubLeftOfHasLinearPairing : HasPairingSubLeft X Y 𝕜 where
  pairing_sub_left x₁ x₀ y := by
    change (HasLinearPairing.pairingLinear (x₁ - x₀)) y =
      (HasLinearPairing.pairingLinear x₁) y - (HasLinearPairing.pairingLinear x₀) y
    exact congrArg (fun g : Module.Dual 𝕜 Y => g y)
      (LinearMap.map_sub
        (HasLinearPairing.pairingLinear : X →ₗ[𝕜] Module.Dual 𝕜 Y) x₁ x₀)

end LinearSub

section LinearZeroRight

variable {𝕜 : Type w} {X : Type u} {Y : Type v}
variable [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- Any linear pairing is automatically compatible with right zero in the second argument. -/
instance instHasPairingZeroRightOfHasLinearPairing : HasPairingZeroRight X Y 𝕜 where
  pairing_zero_right x := by
    change (HasLinearPairing.pairingLinear x) 0 = 0
    simp

end LinearZeroRight

section LinearZeroLeft

variable {𝕜 : Type w} {X : Type u} {Y : Type v}
variable [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- Any linear pairing is automatically compatible with left zero in the first argument. -/
instance instHasPairingZeroLeftOfHasLinearPairing : HasPairingZeroLeft X Y 𝕜 where
  pairing_zero_left y := by
    change (HasLinearPairing.pairingLinear (0 : X)) y = 0
    simp

end LinearZeroLeft

section SwapAddLeft

variable {𝕜 : Type w} {X : Type u} {Y : Type v}
variable [Add X] [Add 𝕜]
variable [HasPairing X Y 𝕜] [HasPairing Y X 𝕜]
variable [HasPairingSwap X Y 𝕜] [HasPairingAddRight Y X 𝕜]

/-- Left-addition compatibility is obtained from swap compatibility plus right-addition
compatibility on the swapped orientation. -/
instance instHasPairingAddLeftOfSwapAddRight : HasPairingAddLeft X Y 𝕜 where
  pairing_add_left x₁ x₂ y := by
    calc
      (⟪x₁ + x₂, y⟫ₚ : 𝕜) = ⟪y, x₁ + x₂⟫ₚ := by
        exact HasPairingSwap.pairing_swap (x₁ + x₂) y
      _ = ⟪y, x₁⟫ₚ + ⟪y, x₂⟫ₚ := HasPairingAddRight.pairing_add_right y x₁ x₂
      _ = ⟪x₁, y⟫ₚ + ⟪x₂, y⟫ₚ := by
        rw [HasPairingSwap.pairing_swap x₁ y, HasPairingSwap.pairing_swap x₂ y]

end SwapAddLeft

section SwapZeroLeft

variable {𝕜 : Type w} {X : Type u} {Y : Type v}
variable [Zero X] [Zero 𝕜]
variable [HasPairing X Y 𝕜] [HasPairing Y X 𝕜]
variable [HasPairingSwap X Y 𝕜] [HasPairingZeroRight Y X 𝕜]

/-- Left-zero compatibility is obtained from swap compatibility plus right-zero compatibility on
the swapped orientation. -/
instance instHasPairingZeroLeftOfSwapZeroRight : HasPairingZeroLeft X Y 𝕜 where
  pairing_zero_left y := by
    calc
      (⟪(0 : X), y⟫ₚ : 𝕜) = ⟪y, (0 : X)⟫ₚ := HasPairingSwap.pairing_swap (0 : X) y
      _ = 0 := pairing_zero_right (X := Y) (Y := X) (𝕜 := 𝕜) y

end SwapZeroLeft

section LiftedCodomain

variable {X : Type u} {Y : Type v} {L : Type w}

/-- Any primitive pairing with values in `L` lifts canonically to the chapter-facing extended
codomain `WithTop (WithBot L)`. -/
instance instHasPairingWithTopBot [HasPairing X Y L] : HasPairing X Y (WithTop (WithBot L)) where
  pairing x y := ((HasPairing.pairing x y : L) : WithTop (WithBot L))

/-- Any primitive pairing with values in `L` lifts canonically to the chapter-facing extended
codomain `WithBot (WithTop L)`. -/
instance instHasPairingWithBotTop [HasPairing X Y L] : HasPairing X Y (WithBot (WithTop L)) where
  pairing x y := ((HasPairing.pairing x y : L) : WithBot (WithTop L))

end LiftedCodomain

section OrderDualCodomain

variable {X : Type u} {Y : Type v} {L : Type w}

/-- Any primitive pairing with values in `L` lifts canonically to the order-dual codomain
`OrderDual L`. -/
instance instHasPairingOrderDual [HasPairing X Y L] : HasPairing X Y (OrderDual L) where
  pairing x y := (⟪x, y⟫ₚ : L)

end OrderDualCodomain

section SubtypeLift

variable {X : Type u} {Y : Type v} {L : Type w}
variable [HasPairing X Y L]
variable {s : Set X}

/-- A pairing restricts canonically to a left subtype domain by evaluating the ambient pairing on
the coerced point. -/
instance instHasPairingSubtypeLeft : HasPairing s Y L where
  pairing x y := ⟪(x : X), y⟫ₚ

variable [HasPairing X X L]

/-- A pairing restricts canonically to subtype domains by evaluating the ambient pairing on the
underlying points. -/
instance instHasPairingSubtype : HasPairing s s L where
  pairing x y := ⟪(x : X), (y : X)⟫ₚ

end SubtypeLift

section ERealCodomain

variable {X : Type u} {Y : Type v}

/-- A real-valued pairing lifts canonically to the chapter's extended-real codomain alias
`EReal`. This bridge keeps downstream Fenchel-conjugacy files on the owner abstraction
`HasPairing X Y ℝ` instead of repeating local alias glue for `EReal = WithBot (WithTop ℝ)`. -/
instance instHasPairingEReal [HasPairing X Y ℝ] : HasPairing X Y EReal :=
  instHasPairingWithBotTop

end ERealCodomain

section ConcretePairings

variable {𝕜 : Type w} {L : Type w}

/-- Evaluation gives the canonical pairing between a point and a scalar-valued function on the
same ambient space. This is the primitive owner behind function-family feasible-set APIs. -/
instance instHasPairingFunctionEval
    (E : Type u) (β : Type v) : HasPairing E (E → β) β where
  pairing x f := f x

@[simp] theorem pairing_functionEval
    {E : Type u} {β : Type v} (x : E) (f : E → β) :
    HasPairing.pairing x f = f x :=
  rfl

/-- Product spaces carry the canonical bilinear pairing obtained by summing the component
pairings. This is the owner bridge for support-function and Fenchel-conjugacy statements on product
spaces. -/
instance instHasPairingProd
    (X₁ : Type*) (X₂ : Type*) (Y₁ : Type*) (Y₂ : Type*)
    [Add L] [HasPairing X₁ Y₁ L] [HasPairing X₂ Y₂ L] :
    HasPairing (X₁ × X₂) (Y₁ × Y₂) L where
  pairing x y := ⟪x.1, y.1⟫ₚ + ⟪x.2, y.2⟫ₚ

@[simp] theorem pairing_prod
    {X₁ : Type*} {X₂ : Type*} {Y₁ : Type*} {Y₂ : Type*}
    [Add L] [HasPairing X₁ Y₁ L] [HasPairing X₂ Y₂ L]
    (x : X₁ × X₂) (y : Y₁ × Y₂) :
    (⟪x, y⟫ₚ : L) = ⟪x.1, y.1⟫ₚ + ⟪x.2, y.2⟫ₚ :=
  rfl

/-- Product modules carry the canonical bilinear pairing obtained by summing the component
linear pairings. -/
instance instHasLinearPairingProd
    (X₁ : Type*) (X₂ : Type*) (Y₁ : Type*) (Y₂ : Type*)
    [CommSemiring 𝕜]
    [AddCommMonoid X₁] [Module 𝕜 X₁]
    [AddCommMonoid X₂] [Module 𝕜 X₂]
    [AddCommMonoid Y₁] [Module 𝕜 Y₁]
    [AddCommMonoid Y₂] [Module 𝕜 Y₂]
    [HasLinearPairing X₁ Y₁ 𝕜] [HasLinearPairing X₂ Y₂ 𝕜] :
    HasLinearPairing (X₁ × X₂) (Y₁ × Y₂) 𝕜 where
  pairingLinear :=
    ((LinearMap.lcomp 𝕜 𝕜 (LinearMap.fst 𝕜 Y₁ Y₂)).comp
        (HasLinearPairing.pairingLinear : X₁ →ₗ[𝕜] Module.Dual 𝕜 Y₁)).coprod
      ((LinearMap.lcomp 𝕜 𝕜 (LinearMap.snd 𝕜 Y₁ Y₂)).comp
        (HasLinearPairing.pairingLinear : X₂ →ₗ[𝕜] Module.Dual 𝕜 Y₂))

/-- Evaluation gives the canonical pairing between a module and its algebraic dual. -/
instance instHasPairingLinearMap
    (E : Type u) [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] :
    HasPairing E (E →ₗ[𝕜] 𝕜) 𝕜 where
  pairing x y := y x

/-- Evaluation also gives the canonical reversed-orientation pairing between an algebraic dual and
its primal module. This keeps dual-as-source theorem surfaces on the same owner layer as
primal-as-source surfaces. -/
instance instHasPairingLinearMapSwap
    (E : Type u) [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] :
    HasPairing (E →ₗ[𝕜] 𝕜) E 𝕜 where
  pairing y x := y x

@[simp] theorem pairing_linearMap_apply
    {E : Type u} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    (x : E) (y : E →ₗ[𝕜] 𝕜) :
    (⟪x, y⟫ₚ : 𝕜) = y x :=
  rfl

@[simp] theorem pairing_linearMap_apply_swap
    {E : Type u} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    (y : E →ₗ[𝕜] 𝕜) (x : E) :
    (⟪y, x⟫ₚ : 𝕜) = y x :=
  rfl

/-- Evaluation gives the canonical bilinear pairing between a module and its algebraic dual. -/
instance instHasLinearPairingLinearMap
    (E : Type u) [CommSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] :
    HasLinearPairing E (E →ₗ[𝕜] 𝕜) 𝕜 where
  pairingLinear :=
    { toFun := fun x =>
        { toFun := fun y => y x
          map_add' := by
            intro y z
            simp
          map_smul' := by
            intro a y
            simp }
      map_add' := by
        intro x z
        ext y
        simp
      map_smul' := by
        intro a x
        ext y
        simp }

/-- Finite coordinate spaces carry the canonical self-pairing given by the coordinate dot product.
This is the owner instance behind the Chapter 22 annihilator constructions on `𝕜^ι`. -/
noncomputable instance instHasLinearPairingPi
    (ι : Type u) [Fintype ι] [CommSemiring 𝕜] :
    HasLinearPairing (ι → 𝕜) (ι → 𝕜) 𝕜 where
  pairingLinear := by
    classical
    exact (dotProductEquiv 𝕜 ι).toLinearMap

/-- The standard real inner product gives the canonical bilinear self-pairing on a real inner
product space. -/
noncomputable instance instHasLinearPairingInner
    (E : Type u) [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] :
    HasLinearPairing E E ℝ where
  pairingLinear := innerₗ E

/-- The canonical real inner-product pairing is continuous in the left variable. -/
instance instHasContinuousPairingInner
    (E : Type u) [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] :
    HasContinuousPairing E E ℝ where
  continuous_pairing_left b := by
    simpa [innerₗ_apply_apply] using continuous_id.inner continuous_const

/-- The canonical real inner-product pairing is symmetric as a bidirectional pairing. -/
instance instHasPairingSwapInner
    (E : Type u) [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] :
    HasPairingSwap E E ℝ where
  pairing_swap x y := by
    simpa [innerₗ_apply_apply] using real_inner_comm y x

/-- Evaluation gives the canonical bilinear pairing between a normed space and its continuous
dual. -/
instance instHasLinearPairingContinuousDual
    (E : Type u) [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    HasLinearPairing E (E →L[𝕜] 𝕜) 𝕜 where
  pairingLinear :=
    { toFun := fun x =>
        { toFun := fun y => y x
          map_add' := by
            intro y z
            simp
          map_smul' := by
            intro a y
            simp }
      map_add' := by
        intro x z
        ext y
        simp
      map_smul' := by
        intro a x
        ext y
        simp }

/-- Evaluation against a continuous functional is continuous in the primal variable. -/
instance instHasContinuousPairingContinuousDual
    (E : Type u) [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    HasContinuousPairing E (E →L[𝕜] 𝕜) 𝕜 where
  continuous_pairing_left y := y.continuous

/-- Evaluation gives the canonical pairing with reversed orientation between a continuous dual
and the primal space. This instance is the stable owner used when conjugate-side subdifferential
graphs are viewed as relations with primal codomain. -/
instance instHasPairingStrongDualPrimal
    (E : Type u) [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    HasPairing (StrongDual 𝕜 E) E 𝕜 where
  pairing xStar x := xStar x

end ConcretePairings
