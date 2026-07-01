import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_19
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_17
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_11
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14

noncomputable section

open scoped Rockafellar

universe u v

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.30.19 identifies Kuhn--Tucker vectors of the primal program `(P)`
  with optimal solutions of the dual program `(P*)`, and dually identifies Kuhn--Tucker vectors
  of `(P*)` with optimal solutions of `(P)`.
- `core/canonical`: the chapter owners already present are
  `IsKuhnTuckerVector`, `IsDualKuhnTuckerVector`, `perturbationFunction`, `objective`,
  `adjoint`, `upperPerturbationFunction`, and the convex closure `cl(·)`.
- `bridge/view`: the source phrase “optimal solution” is rendered directly by the ambient
  optimizer owners `IsMinOn` and `IsMaxOn`, rather than by a new local optimal-solution wrapper
  for generalized primal/dual bifunction programs.

Domain-style sampling used here:
- `IsKuhnTuckerVector` from Definition 6.29.19;
- `objective`, `perturbationFunction`, and `upperPerturbationFunction`;
- `adjoint` from Definition 6.30.14;
- the conjugacy identities of Theorem 6.30.15.

Primitive data vs derived API:
- primitive input: a closed convex bifunction `F : U → X → WithBotTop 𝕜`;
- normality assumptions: the primal perturbation function and the dual upper perturbation function
  agree with their closures at `0`;
- derived API: the two source iff-statements, split atomically.

Layer target: `source-facing`, stated directly on the existing Chapter 6 owners without
introducing a parallel “dual optimal solution” or “dual Kuhn--Tucker package”.
-/

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {UStar : Type*} {XStar : Type*}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
variable [Neg UStar]
variable [Zero XStar] [TopologicalSpace XStar]
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

local notation "p" => perturbationFunction F
local notation "F⋆" => ((adjoint XStar UStar F) : XStar → UStar → WithBotTop 𝕜)
local notation "q" => upperPerturbationFunction F⋆
local notation "f₀" => ((F)₀ : X → WithBotTop 𝕜)
local notation "d₀" => ((F⋆)₀ : UStar → WithBotTop 𝕜)

/- Theorem 6.30.19 is split into two atomic declarations, one for each direction stated
independently in the source. -/

-- Proof sketch: use primal normality to replace `p` by `cl p` at `0`, then apply the conjugacy
-- identity from Theorem 6.30.15 identifying `(adjoint F)₀` with the concave conjugate of
-- `-p`. The Kuhn--Tucker owner `IsKuhnTuckerVector F uStar` is the supporting-hyperplane
-- condition at `0` for `p`, while attainment of the supremum of `(adjoint F)₀` at
-- `uStar` is the equivalent
-- concave-subgradient optimality condition under that conjugacy.
/-- Theorem 6.30.19 (1): if the primal perturbation function and the dual upper perturbation
function are normal at `0`, then a vector `u⋆` is a Kuhn--Tucker vector for the convex program
associated with `F` if and only if it is an optimal solution of the dual concave program,
rendered canonically as a maximizer of the dual zero-slice objective `(F⋆)₀`. -/
theorem isKuhnTuckerVector_iff_isMaxOn_dualObjective_of_normality
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hF_closed : LowerSemicontinuous (Function.uncurry F))
    (hp_normal : p 0 = cl(p) 0)
    (hq_normal : q 0 = (-cl(-q)) 0)
    (uStar : UStar) :
    IsKuhnTuckerVector F uStar ↔
      IsMaxOn d₀ Set.univ uStar := sorry

-- Proof sketch: apply the previous primal-dual clause to the adjoint bifunction `F⋆`.
-- The dual normality hypothesis is exactly the primal normality condition for `F⋆`, while the
-- primal normality hypothesis converts the double-adjoint closure back to the original primal
-- objective. This identifies Kuhn--Tucker vectors for `(P*)` with minimizers of `(F)₀`.
/-- Theorem 6.30.19 (2): under the same two normality assumptions, a vector `x` is a Kuhn--Tucker
vector for the dual program `(P*)`, rendered canonically by the Chapter 6 source-facing owner
`IsDualKuhnTuckerVector`, if and only if it is an optimal solution of the primal program,
rendered canonically as a minimizer of the primal zero-slice objective `(F)₀`. -/
theorem isDualKuhnTuckerVector_iff_isMinOn_objective_of_normality
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hF_closed : LowerSemicontinuous (Function.uncurry F))
    (hp_normal : p 0 = cl(p) 0)
    (hq_normal : q 0 = (-cl(-q)) 0)
    (x : X) :
    IsDualKuhnTuckerVector UStar XStar F x ↔
      IsMinOn f₀ Set.univ x := sorry

end

end Bifunction
