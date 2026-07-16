import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_10
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14

noncomputable section

open scoped Rockafellar

universe u v u' v' w

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 6.30.5 says that for a closed convex bifunction `F`, consistency of
  one side together with strong consistency of the other side forces attainment of the optimal
  value on the merely consistent side.
- `core/canonical`: the existing Chapter 6 owners are `IsConsistent`, `IsStronglyConsistent`,
  `objective`, `adjoint`, `IsDualKuhnTuckerVector`, the normality theorems from
  `Theorem_6_30_17`, and the optimizer/Kuhn--Tucker bridge theorems from `Theorem_6_30_19`.
- `bridge/view`: the source phrase “has an optimal solution” is rendered canonically by the
  optimizer owners `IsMinOn` and `IsMaxOn` for the primal zero-slice objective `(F)₀` and the
  dual zero-slice objective `(F⋆)₀`.

Primary mathematical domain:
- convex duality for closed convex bifunctions on paired scalar-parametric spaces.

Domain-style sampling used here:
- `IsStronglyConsistent` from Definition 6.29.10;
- `IsDualKuhnTuckerVector` from Definition 6.30.17;
- `primalNormal_and_dualNormal_of_sufficientNormalityHypothesis` from Theorem 6.30.17.
- `adjoint` / notation `(·)⋆` from Definition 6.30.14;
- `isDualKuhnTuckerVector_iff_isMinOn_objective_of_normality` and
  `isKuhnTuckerVector_iff_isMaxOn_dualObjective_of_normality` from
  Theorem 6.30.19.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → WithBotTop 𝕜`;
- primitive owners already upstream: primal consistency `IsConsistent F`, dual consistency
  `IsConsistent (F⋆)`, primal strong consistency `IsStronglyConsistent 𝕜 F`, and dual strong
  consistency `IsStronglyConsistent 𝕜 (F⋆)`;
- derived API added here: the two source attainment conclusions, split atomically.

Layer target: `source-facing`, stated directly on the established Chapter 6 owner vocabulary and
the same scalar-parametric pairing ambient layer already used by the Chapter 6 normality and
optimality bridge theorems, with no extra primal-dual program package.
-/

section

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
variable [AddCommGroup XStar] [Module 𝕜 XStar] [TopologicalSpace XStar]
variable [Neg UStar]
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

local notation "F⋆" => ((adjoint XStar UStar F) : XStar → UStar → WithBotTop 𝕜)

-- Proof sketch: dual strong consistency is one of the sufficient normality hypotheses in
-- Theorem 6.30.17, so both primal and dual normality hold. Strong consistency also implies dual
-- consistency, while the assumed primal consistency rules out the exceptional infinite common
-- value. A dual Kuhn--Tucker vector then exists by the chapter's Kuhn--Tucker existence route,
-- and the Chapter 6 primal-optimality bridge
-- `isDualKuhnTuckerVector_iff_isMinOn_objective_of_normality` identifies that vector
-- with a primal minimizer of `(F)₀`.
/-- Corollary 6.30.5 (1): if `F` is a closed convex bifunction, the primal program `(P)` is
consistent, and the adjoint dual program `(P*)` is strongly consistent, then `(P)` has an
optimal solution, rendered canonically as a minimizer of the primal zero-slice objective
`(F)₀`. -/
theorem exists_isMinOn_objective_of_isConsistent_of_isStronglyConsistent_adjoint
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hF_closed : LowerSemicontinuous (Function.uncurry F))
    (hP_consistent : IsConsistent F)
    (hPstar_strong : IsStronglyConsistent 𝕜 F⋆) :
    ∃ x : X, IsMinOn ((F)₀ : X → WithBotTop 𝕜) Set.univ x := sorry

-- Proof sketch: primal strong consistency gives the sufficient normality hypothesis from
-- Theorem 6.30.17, hence both normality identities at `0`. Strong consistency also implies
-- primal consistency, and the assumed dual consistency makes the common primal-dual value finite.
-- A primal Kuhn--Tucker vector then exists by the chapter's Kuhn--Tucker existence route, and
-- the Chapter 6 dual-optimality bridge
-- `isKuhnTuckerVector_iff_isMaxOn_dualObjective_of_normality` identifies such a
-- vector with a maximizer of the dual zero-slice objective `(F⋆)₀`.
/-- Corollary 6.30.5 (2): if `F` is a closed convex bifunction, the primal program `(P)` is
strongly consistent, and the adjoint dual program `(P*)` is consistent, then `(P*)` has an
optimal solution, rendered canonically as a maximizer of the dual zero-slice objective
`(F⋆)₀`. -/
theorem
    exists_isMaxOn_objective_adjoint_of_isStronglyConsistent_of_isConsistent_adjoint
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hF_closed : LowerSemicontinuous (Function.uncurry F))
    (hP_strong : IsStronglyConsistent 𝕜 F)
    (hPstar_consistent : IsConsistent F⋆) :
    ∃ uStar : UStar, IsMaxOn ((F⋆)₀ : UStar → WithBotTop 𝕜) Set.univ uStar := sorry

end

end Bifunction
