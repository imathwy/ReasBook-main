import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_11
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_13_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped Rockafellar
open Function

section

variable {𝕜 : Type*} {X : Type u} {Y : Type v}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X] [FiniteDimensional 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] [HasContinuousPairing X Y 𝕜]

local instance : HasPairing Y X 𝕜 := HasPairing.swap (X := X) (Y := Y)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.6 identifies the closure of the generated function of
  `δ[𝕜](· | C) + 1` for a nonempty convex set `C ⊆ X` with the support function
  `δᵛ[WithTopBot 𝕜](· | Cᵒ[𝕜])` of its polar subset `Cᵒ[𝕜] ⊆ Y`.
- `core/canonical`: the owner constructions in this domain are `sublinearHull`,
  `lowerSemicontinuousHull`, `supportFunction`, and `Set.polar`; the owner theorem driving the
  specialization is
  `lowerSemicontinuousHull_generatedBy_eq_supportFunction_nonpositiveSublevel_convexConjugate`.
- `bridge/view`: Text 5.4.11 provides the generated-function owner for `δ[𝕜](· | C) + 1`, and
  Text 14.0.5 identifies the corresponding nonpositive conjugate sublevel set with `Cᵒ[𝕜]`.

Domain-style sampling used here:
- `sublinearHull (δ[𝕜](· | C) + 1)` from `Text_5_4_11`;
- `lowerSemicontinuousHull` / the chapter notation `cl(·)` from `Text_7_0_4`;
- `Set.polar` / the chapter notation `Cᵒ[𝕜]` from `Text_14_0_5`;
- `lowerSemicontinuousHull_generatedBy_eq_supportFunction_nonpositiveSublevel_convexConjugate`
  from `Theorem_13_5`.

Primitive data vs derived API:
- primitive inputs: the set `C`, together with the source-essential hypotheses `Convex 𝕜 C` and
  `C.Nonempty`;
- derived output: the support-function description of the `WithTopBot 𝕜`-valued closure of the
  generated function of `δ[𝕜](· | C) + 1`, obtained by specializing the owner theorem from
  `Theorem_13_5` along `Text_5_4_11` and the chapter polar owner from `Text_14_0_5` (on the
  dual/primal swapped pairing orientation).

Ambient minimization: the theorem only uses the owner constructions above, so the public API lives
at the canonical ambient level of a finite-dimensional `𝕜`-module paired with a dual-side
`𝕜`-module by a continuous linear pairing, instead of a concrete real/self-dual model.

Layer target: `bridge/view`, stated directly in the chapter owners `cl(·)`, `δ[𝕜](· | ·)`,
`δᵛ[WithTopBot 𝕜](· | ·)`, and `Cᵒ[𝕜]`, without any local wrapper around the generated function or
polar constructions.
-/

-- Proof sketch: apply Text 5.4.11 to the source function `x ↦ δ(x | C) + 1`, whose generated
-- positively homogeneous convex function is the gauge-side owner used in the proof route. Then use
-- Theorem 13.5 for that generated function. Its conjugate is `δᵛ(· | C) - 1`, so the owner-side
-- nonpositive sublevel set is exactly `Cᵒ` by Text 14.0.5, yielding the support-function formula.
/-- Text 14.0.6: for a nonempty convex set in a finite-dimensional topological `𝕜`-module
carrying a continuous linear pairing to a dual-side module, the closure of the generated function
`sublinearHull (δ[𝕜](· | C) + 1)` is the support function
`δᵛ[WithTopBot 𝕜](· | Cᵒ[𝕜])` of its polar. -/
theorem lowerSemicontinuousHull_generatedBy_indicator_add_one_eq_supportFunction_polar
    (C : Set X) (hC_convex : Convex 𝕜 C) (hC_nonempty : C.Nonempty) :
    cl(sublinearHull (δ[𝕜](· | C) + 1)) =
      (δᵛ(· | (Cᵒ[𝕜] : Set Y)) : X → WithTopBot 𝕜) := sorry

end
