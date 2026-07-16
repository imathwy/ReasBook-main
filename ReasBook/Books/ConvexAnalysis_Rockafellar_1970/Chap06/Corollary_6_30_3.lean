import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_11
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14

noncomputable section

open Filter
open scoped Rockafellar

universe u v u' v' w

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: the present corollary states that, except when both the primal and dual programs
  are inconsistent, the liminf at `0` of the primal perturbation function `inf F` equals the dual
  value `sup F* 0`, and the limsup at `0` of the dual perturbation function `sup F*` equals the
  primal value `inf F 0`.
- `core/canonical`: the relevant owner layer is already present as `perturbationFunction`,
  `upperPerturbationFunction`/`supᵇ(·)`, `adjoint`, `IsConsistent`, and the filter-side owners
  `liminf` and `limsup`.
- `bridge/view`: the source notations `inf F` and `sup F*` are rendered canonically by
  `perturbationFunction F` and `supᵇ(F⋆)`.

Domain-style sampling used here:
- `perturbationFunction` and `IsConsistent` from Definition 6.29.1;
- `upperPerturbationFunction` from Definition 6.30.11;
- `adjoint` from Definition 6.30.14;
- the zero-value identities from Corollary 6.30.2;
- the inconsistency criteria from Corollary 6.30.1.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → WithBotTop 𝕜` on paired spaces
  `(U, UStar)` and `(X, XStar)`;
- primitive owners already upstream: `perturbationFunction F`,
  `supᵇ(F⋆)`, and the primal/dual consistency predicates;
- derived API added here: the two neighborhood-limit identities at the origin.

Layer target: `source-facing`, stated directly on the chapter's canonical owners without adding a
separate wrapper for the primal-dual program pair.
-/

section

variable {𝕜 : Type w}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module 𝕜 UStar]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

-- Proof sketch: apply the general identity
-- `(cl (perturbationFunction F)) 0 = liminf (perturbationFunction F) (nhds 0)` away from the
-- exceptional `⊥/⊤` case, then rewrite `(cl (perturbationFunction F)) 0` by Corollary 6.30.2.
-- Corollary 6.30.1 rules out the exceptional case as soon as either the primal or the dual
-- program is consistent.
/-- Corollary 6.30.3 (1): if either the primal or the dual generalized convex program attached to
`F` is consistent, then the liminf at `0` of the primal perturbation function equals the dual
upper perturbation value at `0`, i.e.
`liminf_{u → 0} (inf F)(u) = (sup F^*)(0)`. -/
theorem liminf_perturbationFunction_eq_upperPerturbationFunction_adjoint_zero_of_primal_or_dual_consistent
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hconsistent :
      IsConsistent F ∨ IsConsistent ((F⋆) : XStar → UStar → WithBotTop 𝕜)) :
    liminf (perturbationFunction F) (nhds (0 : U)) =
      supᵇ(((F⋆) : XStar → UStar → WithBotTop 𝕜)) (0 : XStar) := sorry

-- Proof sketch: apply the concave-side identity
-- `concaveClosure (upperPerturbationFunction (adjoint F)) 0 =
-- perturbationFunction F 0` from Corollary 6.30.2 together with the general formula expressing a
-- concave closure value as a limsup at the base point away from the exceptional `⊤/⊥` case.
-- The same consistency disjunction excludes that exceptional case via Corollary 6.30.1.
/-- Corollary 6.30.3 (2): if either the primal or the
dual generalized convex program attached to the closed convex bifunction `F` is consistent, then
the limsup at `0` of the dual upper perturbation function equals the primal perturbation value at
`0`, i.e. `limsup_{x^* → 0} (sup F^*)(x^*) = (inf F)(0)`. -/
theorem limsup_upperPerturbationFunction_adjoint_eq_perturbationFunction_zero_of_primal_or_dual_consistent
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hF_closed : LowerSemicontinuous (Function.uncurry F))
    (hconsistent :
      IsConsistent F ∨ IsConsistent ((F⋆) : XStar → UStar → WithBotTop 𝕜)) :
    limsup (supᵇ(((F⋆) : XStar → UStar → WithBotTop 𝕜))) (nhds (0 : XStar)) =
      perturbationFunction F (0 : U) := sorry

end

end Bifunction
