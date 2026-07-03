import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_14_5_1 (from Chap03) -/
section

open Bornology
open scoped Rockafellar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage:
- `source-facing`: Corollary 14.5.1 identifies boundedness of a set or of its polar with the
  origin lying in the interior of the dual set.
- `core/canonical`: the owner abstractions already present in the project are the set polar
  `Set.polar`, the canonical boundedness predicate `Bornology.IsBounded`, the structural owner
  theorems `Set.convex_polar` and `Set.polar_polar_eq`, and the interior owner theorem
  `Convex.mem_interior_iff_forall_exists_pos_add_smul_mem`.
- `bridge/view`: Rockafellar's notation `Cᵒ` is rendered directly by `Set.polar C`, and the two
  source clauses are exposed as separate atomic theorems on the `Convex` and `Set` owner surfaces.

Domain-style sampling used here:
- `Set.polar` and `Set.polar_closure` from `Text_14_0_5`;
- `Set.convex_polar` and `Set.polar_polar_eq` from `Theorem_14_5`;
- `Convex.mem_interior_iff_forall_exists_pos_add_smul_mem` from `Corollary_6_4_1`.
- mathlib's nearby dual-space polar owners `WeakDual.polar` and `LinearMap.polar`, inspected as
  neighbors but not reused because they formalize dual-valued or bilinear-form polars rather than
  the chapter's support-function sublevel set `Set.polar`.

Primitive data vs derived API:
- clause (1) primitive input: a convex set `C : Set E`;
- clause (1) derived output: boundedness of `Set.polar C` versus `0 ∈ interior C`;
- clause (2) primitive input: an arbitrary set `C : Set E`;
- clause (2) derived output: boundedness of `C` versus `0 ∈ interior (Set.polar C)`.

Layer target:
- clause (1) stays `source-facing`, but it belongs on the `Convex` owner abstraction rather than
  as a parallel global theorem carrying convexity as loose data;
- clause (2) stays `source-facing` on the `Set` owner surface, with no extra closedness or
  convexity packaging because those are mathematically redundant in the polar-interior criterion.

Ambient refinement:
- the supporting owner theorems already live on arbitrary finite-dimensional real inner-product
  spaces, so this file is stated at that intrinsic layer rather than in the coordinate model
  `EuclideanSpace ℝ (Fin n)`;
- the proof route for clause (1) should pass through `closure C`, but the public API should use the
  existing owner theorem `Set.polar_closure` instead of restating closure invariance through the
  support-function presentation;
- clause (1) needs the ambient space to be nontrivial. In the zero-dimensional case `E = PUnit`,
  the empty set has polar `univ`, which is bounded, while `0 ∉ interior ∅`, so the textbook
  bounded-polar/interior criterion is not valid without that ambient hypothesis.
-/

namespace Convex

variable [Nontrivial E]
variable {C : Set E}

-- Proof sketch: replace `C` by `closure C`. The owner identity `Set.polar_closure` gives
-- `(closure C)ᵒ[ℝ] = Cᵒ[ℝ]`, so Theorem 14.5 applies to `closure C`. Corollary 13.2.2 identifies
-- boundedness of `Set.polar C` with finiteness of its support function in every direction, and
-- Corollary 6.4.1 transports the resulting interior statement back from `closure C` to `C` using
-- convexity.
/-- Corollary 14.5.1 (1): on a nontrivial finite-dimensional real inner-product space, the polar
set `Cᵒ[ℝ]` of a convex set `C` is bounded if and only if the origin lies in `interior C`.
Specializing to `EuclideanSpace ℝ (Fin n)` with `n ≠ 0` recovers the textbook `R^n` statement. -/
theorem isBounded_polar_iff_zero_mem_interior (hC : Convex ℝ C) :
    IsBounded ((Cᵒ[ℝ] : Set E)) ↔ (0 : E) ∈ interior C := sorry

end Convex

namespace Set

-- Proof sketch: if `C` is bounded, choose `R > 0` with `‖x‖ ≤ R` for all `x ∈ C`. Then every
-- `xStar` with `‖xStar‖ < R⁻¹` satisfies `⟪x, xStar⟫ ≤ 1` on `C` by Cauchy-Schwarz, so a ball
-- around `0` lies in `Cᵒ[ℝ]`. Conversely, if a ball of radius `ε > 0` around `0` lies in
-- `Cᵒ[ℝ]`, then
-- for each `x ∈ C`, testing the polar inequality at `ε • ‖x‖⁻¹ • x` (or `0` when `x = 0`)
-- yields `‖x‖ ≤ ε⁻¹`, hence `C` is bounded.
/-- Corollary 14.5.1 (2): on a finite-dimensional real inner-product space, a set `C` is bounded
if and only if the origin lies in the interior of its polar set `Cᵒ[ℝ]`. Specializing to
`EuclideanSpace ℝ (Fin n)` recovers the textbook `R^n` statement. -/
theorem isBounded_iff_zero_mem_interior_polar
    (C : Set E) :
    IsBounded C ↔ (0 : E) ∈ interior ((Cᵒ[ℝ] : Set E)) := sorry

end Set

end

/-! ### Theorem_14_5 (from Chap03) -/
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
