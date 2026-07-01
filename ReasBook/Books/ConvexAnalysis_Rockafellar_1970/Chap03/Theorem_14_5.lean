import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_9_7_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ENNReal NNReal Rockafellar

section

universe u v

variable {𝕜 : Type*} {X : Type u} {Y : Type v}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace X] [TopologicalSpace Y]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

local instance : HasPairing Y X 𝕜 := HasPairing.swap (X := X) (Y := Y)

-- Proof sketch: write `Cᵒ[𝕜]` as the support-function sublevel set
-- `{y | δᵛ[WithBotTop 𝕜](y | C) ≤ 1}` and use closedness of that sublevel.
namespace Set

/-- The polar of any set is closed; in particular, the polar of a closed convex
set containing `0` is closed. -/
theorem isClosed_polar
    [HasContinuousPairing X Y 𝕜]
    (C : Set X) :
    IsClosed (Cᵒ[𝕜] : Set Y) := sorry

-- Proof sketch: each half-space `{y | ⟪y, x⟫ ≤ 1}` is convex and `Cᵒ[𝕜]` is their
-- intersection over `x ∈ C`.
/-- The polar of any set is convex; in particular, the polar of a closed convex
set containing `0` is convex. -/
theorem convex_polar
    (C : Set X) :
    Convex 𝕜 (Cᵒ[𝕜] : Set Y) := sorry

-- Proof sketch: `0` satisfies `⟪0, x⟫ ≤ 1` for every `x ∈ C`.
/-- The polar of any set contains the origin; in particular, the polar of a
closed convex set containing `0` contains `0`. -/
theorem zero_mem_polar
    (C : Set X) :
    (0 : Y) ∈ (Cᵒ[𝕜] : Set Y) := sorry

end Set

section

namespace Set

section
variable [FiniteDimensional 𝕜 X]
variable {C : Set X}
variable (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C) (h0C : (0 : X) ∈ C)

-- Proof sketch: the preceding three clauses show that `Cᵒ[ℝ]` is a closed convex set containing
-- `0`. The support-function description of a closed convex set then identifies the bipolar
-- `(Cᵒ[ℝ])ᵒ[ℝ]` with `C`.
/-- Theorem 14.5: a closed convex set containing the origin is equal to its bipolar. -/
theorem polar_polar_eq
    (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C) (h0C : (0 : X) ∈ C)
    :
    ((Cᵒ[𝕜] : Set Y)ᵒ[𝕜] : Set X) = C := sorry

end

end Set

section
variable {X : Type u} {Y : Type v}
variable [TopologicalSpace X] [AddCommGroup X] [Module ℝ X] [IsTopologicalAddGroup X]
variable [ContinuousSMul ℝ X] [FiniteDimensional ℝ X]
variable [AddCommMonoid Y] [Module ℝ Y]
variable [HasLinearPairing X Y ℝ] [HasContinuousPairing X Y ℝ]

local instance : HasPairing Y X ℝ := HasPairing.swap (X := X) (Y := Y)

variable {C : Set X}
variable (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_nonempty : C.Nonempty)

-- Proof sketch: Text 14.0.6 identifies the lower semicontinuous hull of the gauge with the
-- support function of the polar. Corollary 9.7.1 makes the extended gauge lower semicontinuous for
-- closed convex `C`, so the hull can be removed; only nonemptiness remains from Text 14.0.6.
/-- For a nonempty closed convex set in a finite-dimensional real topological module paired with a
dual-side module, the gauge `γ(· | C)` (viewed in `EReal`) is the support function of its polar.
-/
theorem egauge_eq_supportFunction_polar
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_nonempty : C.Nonempty)
    (x : X) :
    (γ(x | C) : EReal) = δᵛ[EReal](x | (Cᵒ[ℝ] : Set Y)) := sorry

end

section
variable {X : Type u} {Y : Type v}
variable [TopologicalSpace X] [AddCommGroup X] [Module ℝ X] [IsTopologicalAddGroup X]
variable [ContinuousSMul ℝ X] [FiniteDimensional ℝ X]
variable [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y] [IsTopologicalAddGroup Y]
variable [ContinuousSMul ℝ Y] [FiniteDimensional ℝ Y]
variable [HasLinearPairing X Y ℝ] [HasContinuousPairing X Y ℝ]

local instance : HasPairing Y X ℝ := HasPairing.swap (X := X) (Y := Y)

variable {C : Set X}
variable (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (h0C : (0 : X) ∈ C)

-- Proof sketch: apply the previous clause to `Cᵒ[ℝ]`, which is closed, convex, and contains `0`
-- by clauses (1)–(3), and then rewrite `(Cᵒ[ℝ])ᵒ[ℝ] = C` using the bipolar identity.
/-- Dually, for a closed convex set containing the origin in a finite-dimensional real paired
ambient, the gauge of `Cᵒ[ℝ]` (viewed in `EReal`) is the support function of `C`. -/
theorem egauge_polar_eq_supportFunction
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (h0C : (0 : X) ∈ C)
    (y : Y) :
    (γ(y | (Cᵒ[ℝ] : Set Y)) : EReal) = δᵛ[EReal](y | C) := sorry

end

end

end
