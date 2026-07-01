import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_12
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_11
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14

noncomputable section

open scoped Rockafellar

universe u v v'

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 6.30.2 evaluates at `0` the primal perturbation function `inf F`,
  the dual upper perturbation function `sup F*`, and the zero-slice objectives `F₀` and `F*₀`,
  concluding the primal-dual value inequality `inf F0 ≥ sup F*0`.
- `core/canonical`: the owner declarations already present in Chapter 6 are
  `perturbationFunction`, `upperPerturbationFunction`/`supᵇ(·)`, `objective`, `adjoint`,
  `concaveClosure`, and the convex closure `cl(·)`.
- `bridge/view`: the source writes `sup F*0` and `inf F0`; these are rendered canonically as
  `sSup (Set.range ((F⋆)₀))` and `sInf (Set.range ((F)₀))`.

Domain-style sampling used here:
- `perturbationFunction` and `objective` from Definitions 6.29.1 and 6.29.12;
- the scoped zero-slice notation `(·)₀` from Definition 6.29.12;
- `upperPerturbationFunction` / `supᵇ(·)` from Definition 6.30.11;
- `adjoint` from Definition 6.30.14;
- the conjugacy identities of Theorem 6.30.15.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → WithBotTop 𝕜`;
- primitive owners already upstream: `perturbationFunction F`,
  `supᵇ(F⋆)`, `(F)₀`, and `(F⋆)₀`;
- derived API added here: the five value identities at `0` and the resulting primal-dual
  inequality.

Layer target: `source-facing`, stated directly on the established Chapter 6 owners with no extra
program package or wrapper for optimal values.
-/

section ClPrimalEqDualAtZero

variable {𝕜 : Type*} {U : Type u} {X : Type v} {XStar : Type v'}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U] [FiniteDimensional 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [Zero XStar]
variable [HasLinearPairing U U 𝕜] [HasContinuousPairing U U 𝕜]
variable [HasPairing X XStar 𝕜]
variable (F : U → X → WithBotTop 𝕜)

local notation "F⋆" => adjoint XStar U F

-- Proof sketch: apply the first closed-value identity from Theorem 6.30.15 to `F` and evaluate
-- the resulting concave-conjugate formula at `0`; at the origin, the concave conjugate rewrites
-- the dual zero-slice objective as the upper perturbation value
-- `supᵇ(F⋆) 0`.
/-- Corollary 6.30.2 (1): for a convex bifunction `F`, the closure of the primal perturbation
value at `0` equals the dual upper perturbation value at `0`, i.e.
`(cl (inf F))(0) = (sup F^*)(0)`. -/
theorem cl_perturbationFunction_zero_eq_upperPerturbationFunction_adjoint_zero
    (hF_convex : (Function.uncurry F).IsConvex 𝕜) :
    cl(perturbationFunction F) 0 =
      supᵇ(F⋆) 0 := sorry

end ClPrimalEqDualAtZero

-- Proof sketch: this is the owner theorem
-- `Bifunction.upperPerturbationFunction_zero_eq_sSup_range_objective` specialized to `F⋆`.
/- Corollary 6.30.2 (2): the dual upper perturbation value at `0` is the supremum of the dual
zero-slice objective `F^*_0`, i.e. `(sup F^*)(0) = sup F^*0`. -/
recall upperPerturbationFunction_zero_eq_sSup_range_objective

section ConcaveClosureDualEqPrimalAtZero

variable {𝕜 : Type*} {U : Type u} {X : Type v} {XStar : Type v'}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U] [FiniteDimensional 𝕜 U]
variable [TopologicalSpace X] [AddCommMonoid X] [Module 𝕜 X]
variable [TopologicalSpace XStar] [Zero XStar]
variable [HasLinearPairing U U 𝕜] [HasContinuousPairing U U 𝕜]
variable [HasPairing X XStar 𝕜]
variable (F : U → X → WithBotTop 𝕜)

local notation "F⋆" => adjoint XStar U F

-- Proof sketch: combine the second closed-value identity from Theorem 6.30.15 with the
-- graph-function closedness of `F`, then evaluate the resulting conjugate-side equality at `0`.
/-- Corollary 6.30.2 (3): for a closed convex bifunction `F`, the concave closure of the dual
upper perturbation function at `0` equals the primal perturbation value at `0`. -/
theorem concaveClosure_upperPerturbationFunction_adjoint_zero_eq_perturbationFunction_zero
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hF_closed : LowerSemicontinuous (Function.uncurry F)) :
    concaveClosure (supᵇ(F⋆)) 0 =
      perturbationFunction F 0 := sorry

end ConcaveClosureDualEqPrimalAtZero

-- Proof sketch: unfold the perturbation function at `0`; by definition it is the infimum over
-- the `X`-slice `x ↦ F 0 x`, which is exactly the primal zero-slice objective `(F)₀`.
/- Corollary 6.30.2 (4) is already the canonical owner theorem
`Bifunction.perturbationFunction_zero_eq_sInf_range`. -/
recall perturbationFunction_zero_eq_sInf_range

section PrimalValueGeDualValue

variable {𝕜 : Type*} {U : Type u} {X : Type v} {XStar : Type v'}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [Zero XStar]
variable [HasPairing U U 𝕜] [HasPairing X XStar 𝕜]
variable (F : U → X → WithBotTop 𝕜)

local notation "F⋆" => adjoint XStar U F

-- Proof sketch: combine clauses (1), (2), and the owner theorem
-- `perturbationFunction_zero_eq_sInf_range` with the basic inequality
-- `cl(perturbationFunction F) 0 ≤ perturbationFunction F 0`, then rewrite both sides through the
-- objective-range formulas.
/-- Corollary 6.30.2 (5): the primal optimal value dominates the dual optimal value,
`inf F0 ≥ sup F^*0`. -/
theorem sInf_range_objective_ge_sSup_range_objective_adjointFunction
    (hF_convex : (Function.uncurry F).IsConvex 𝕜) :
    sInf (Set.range ((F)₀)) ≥
      sSup (Set.range ((F⋆)₀)) := sorry

end PrimalValueGeDualValue

end Bifunction
