import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_4
import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem_37_2

noncomputable section

universe u u' v v'

open Bifunction
open scoped Rockafellar

namespace SaddleFunction

section

variable {𝕜 : Type*} {U : Type u} {UStar : Type u'} {X : Type v} {XStar : Type v'}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [HasPairing U UStar (WithTopBot 𝕜)] [HasPairing X XStar (WithTopBot 𝕜)]

local instance : HasPairing XStar X (WithTopBot 𝕜) := HasPairing.swap
local notation "lowerConjugate" =>
  (Bifunction.lowerConjugate : (U → X → WithTopBot 𝕜) → UStar → XStar → WithTopBot 𝕜)

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 37.2.1 converts the relative-interior-at-the-origin condition for the
  second and first domain factors of the conjugate saddle-function into the absence of a common
  recession direction for the slice families `K(u, ·)` and `-K(·, v)`.
- `core/canonical`: the owner abstractions already present upstream are the Chapter 37 conjugate
  owner `lowerConjugate K` and its Chapter 34 coordinate-domain factors
  `dom₁ (lowerConjugate K)` and `dom₂ (lowerConjugate K)`, together with
  `SaddleFunction.dom₁`, `SaddleFunction.dom₂`, convex conjugation `(·)⋆`, and, under
  convex/proper hypotheses on a slice, the Chapter 2 bridge owner `Function.recessionCone ((·)₀⁺)`.
- `bridge/view`: the source wording “no common nonzero recession direction” is kept directly via
  the source-facing owner `Function.RecedesInDirection`; the cone language from Chapter 2 remains
  only the internal bridge to the one-variable criteria in Chapters 3 and 6.

Primary mathematical domain:
- existence criteria for saddle-values of closed proper concave-convex saddle-functions, via
  conjugate-domain geometry and slice recession behavior.

Domain-style sampling used here:
- `Bifunction.lowerConjugate` from `Chap07.Definition_37_1_1`;
- `SaddleFunction.dom₁` and `SaddleFunction.dom₂` from `Chap07.Defn_34_2`;
- `SaddleFunction.supportFunction_conjugateDom₂_eq_iSup_iSup_translate_sub` and
  `SaddleFunction.neg_supportFunction_neg_conjugateDom₁_eq_iInf_iInf_translate_sub` from
  `Chap07.Theorem_37_2`;
- `Function.RecedesInDirection` and
  `Function.recedesInDirection_iff_mem_recessionCone` from `Chap06.Definition_6_27_4`;
- `Function.recessionCone` from `Chap02.Definiton_8_5_0`.

Primitive data vs derived API:
- primitive source data: the saddle-function `K` together with the source hypotheses
  `IsClosed K`, `IsProper K`, and `IsConcaveConvex 𝕜 K`;
- primitive owner data reused from the chapter: `dom₁ (lowerConjugate K)`,
  `dom₂ (lowerConjugate K)`, `dom₁ K`, and `dom₂ K`;
- derived API: the two no-common-slice-recession-direction criteria below, stated directly with
  `Function.RecedesInDirection` on the source-facing side and on the canonical Chapter 37 owners
  on the conjugate-domain side.

Layer target: `source-facing`.

Ambient refinement:
- the statement surface is kept at the Chapter 34/37 ordered-module and pairing layer with
  scalar-annotated relative interior `ri[𝕜](·)`;
- dual evaluation is exposed directly through explicit pairing owners
  `HasPairing U UStar (WithTopBot 𝕜)` and `HasPairing X XStar (WithTopBot 𝕜)` rather than by
  fixing an `InnerProductSpace` model.
-/

-- Proof sketch: Theorem 37.2 expresses the support function of the canonical second coordinate
-- `dom₂ (lowerConjugate K)` as the pointwise supremum of the recession functions of the convex
-- slices `K(u, ·)` over `u ∈ ri[𝕜](dom₁ K)`. Corollary 13.3.4 at `xStar = 0` supplies the
-- one-slice relative-interior/recession bridge, and Chapter 6 identifies slice recession
-- directions with nonzero members of the corresponding slice recession cone. This yields the
-- source-facing "no common nonzero recession direction" criterion.
section Dom₂

variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]

/-- Corollary 37.2.1, second-variable clause: for a closed proper concave-convex saddle-function
`K`, the origin lies in the relative interior of the second conjugate-domain factor exactly when
the convex slice family `K(u, ·)` with `u ∈ ri[𝕜](dom₁ K)` has no common nonzero recession
direction. The conjugate-domain side is written on the Chapter 37 owner
`dom₂ (lowerConjugate K)`, while the slice side uses the source-facing owner
`Function.RecedesInDirection`. -/
theorem zero_mem_ri_dom₂_lowerConjugate_iff_no_common_recession_direction
    {K : U → X → WithTopBot 𝕜}
    (hK_closed : IsClosed K) (hK_proper : IsProper K)
    (hK_concaveConvex : IsConcaveConvex 𝕜 K) :
    (0 : XStar) ∈ ri[𝕜](dom₂ (lowerConjugate K)) ↔
      ¬ ∃ y : X, ∀ u ∈ ri[𝕜](dom₁ K), (K u).RecedesInDirection 𝕜 y := by
  sorry

end Dom₂

-- Proof sketch: apply the previous argument to the first-variable family by passing to the convex
-- slices `fun u ↦ -K u v` indexed by `v ∈ ri[𝕜](dom₂ K)`. Again Chapter 6 converts the source
-- no-common-direction wording into the Chapter 2 recession-cone owner used behind the Chapter 3
-- relative-interior criterion.
section Dom₁

variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module 𝕜 UStar]

/-- Corollary 37.2.1, first-variable clause: for a closed proper concave-convex saddle-function
`K`, the origin lies in the relative interior of the first conjugate-domain factor exactly when
the convex slice family `-K(·, v)` with `v ∈ ri[𝕜](dom₂ K)` has no common nonzero recession
direction. The conjugate-domain side is written on the Chapter 37 owner
`dom₁ (lowerConjugate K)`, while the slice side uses the source-facing owner
`Function.RecedesInDirection`. -/
theorem zero_mem_ri_dom₁_lowerConjugate_iff_no_common_recession_direction
    {K : U → X → WithTopBot 𝕜}
    (hK_closed : IsClosed K) (hK_proper : IsProper K)
    (hK_concaveConvex : IsConcaveConvex 𝕜 K) :
    (0 : UStar) ∈ ri[𝕜](dom₁ (lowerConjugate K)) ↔
      ¬ ∃ y : U, ∀ v ∈ ri[𝕜](dom₂ K), (fun u ↦ -K u v).RecedesInDirection 𝕜 y := by
  sorry

end Dom₁

end

end SaddleFunction
