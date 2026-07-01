import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_11
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14

noncomputable section

open scoped Rockafellar

universe u v u' v'

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.30.16 states that for a closed convex bifunction program `(P)` and
  its adjoint dual `(P*)`, primal normality, dual normality, and equality of the primal and dual
  values are equivalent.
- `core/canonical`: the relevant Chapter 6 owners already present are
  `perturbationFunction`, `upperPerturbationFunction`, `adjoint`, and the Chapter 2
  closure owners `cl(·)` and `- cl(- ·)`.
- `bridge/view`: the shortest faithful theorem surface keeps the source point-value equation
  directly as `perturbationFunction F 0 = q 0`.

Primary mathematical domain:
- convex duality for closed convex bifunctions on scalar-parametric paired spaces.

Domain-style sampling used here:
- `perturbationFunction` from Definition 6.29.1;
- `upperPerturbationFunction` from Definition 6.30.11;
- `adjoint` from Definition 6.30.14;
- the closure owners `cl(·)` and `- cl(- ·)` at the primal/dual base points.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → WithBotTop 𝕜`;
- primitive owner expressions already upstream: `perturbationFunction F`,
  `upperPerturbationFunction F⋆`, and their closure formulas at `0`;
- derived API added here: the TFAE equivalence between primal normality, dual normality, and
  zero duality gap.

Layer target: `bridge/view`, stated directly on the canonical owner expressions rather than
introducing a new wrapper for primal or dual programs.

Ambient-vs-intrinsic topology choice:
- this theorem is intentionally phrased with the ambient closure owners `cl(·)` and `- cl(- ·)`
  because those are the Chapter 6 normality owners used by the surrounding closure/conjugacy
  bridge files; no project-level intrinsic/relative replacement owner is established nearby.
-/

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup UStar] [Module 𝕜 UStar]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable [HasLinearPairing X XStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

local notation "F⋆" => adjoint XStar UStar F
local notation "p" => perturbationFunction F
local notation "q" => upperPerturbationFunction F⋆

-- Proof sketch: once the closed-convex bridge identities
-- `cl(p) 0 = q 0` and `(- cl(-q)) 0 = p 0` are available, each normality clause is equivalent
-- to the shared middle equality `p 0 = q 0`, so the three source conditions lie in one
-- `List.TFAE` class. The adjoint owner is parameterized by the explicit dual-side space `UStar`
-- rather than a self-dual `U`.
/-- Theorem 6.30.16: for a closed convex bifunction `F`, the following are equivalent:
(a) the convex program `(P)` associated with `F` is normal, rendered canonically as
`p 0 = cl(p) 0`;
(b) the dual concave program `(P*)` is normal, rendered canonically as
`q 0 = (- cl(-q)) 0`;
(c) `inf F 0 = sup F* 0`, rendered canonically as `p 0 = q 0`, equivalently equality of the
primal and dual optimal values. -/
theorem primalNormal_dualNormal_zeroDualityGap_tfae
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hF_closed : LowerSemicontinuous (Function.uncurry F)) :
    List.TFAE
      [p 0 = cl(p) 0,
        q 0 = (- cl(-q)) 0,
        p 0 = q 0] := sorry

end

end Bifunction
