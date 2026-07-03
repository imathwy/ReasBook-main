

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_37_2_1 (from Chap07) -/
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

/-! ### Theorem_37_2 (from Chap07) -/
noncomputable section

universe u u' v v'

open scoped Rockafellar

namespace SaddleFunction

section

open Bifunction

variable {𝕜 : Type*} {U : Type u} {UStar : Type u'} {X : Type v} {XStar : Type v'}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [HasPairing U UStar (WithTopBot 𝕜)] [HasPairing X XStar (WithTopBot 𝕜)]

local instance : HasPairing XStar X (WithTopBot 𝕜) := HasPairing.swap

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 37.2 identifies the two coordinate domains `C*` and `D*` common to
  the saddle-functions conjugate to a closed proper concave-convex `K` through explicit support
  function formulas written only in terms of translation increments of `K`.
  Core owners: conjugate owner `lowerConjugate K`, the Chapter 34 domain owners
  `SaddleFunction.dom₁` and `SaddleFunction.dom₂`, the support function `δᵛ(· | ·)`,
  and the recession-function owners from Theorems 8.5 and 13.3.
- `bridge/view`: the source symbols `C*` and `D*` are used only as textbook labels for the two
  coordinate domains of `lowerConjugate K`, so the theorem surface should reuse
  `dom₁ (lowerConjugate K)` and `dom₂ (lowerConjugate K)` directly instead of introducing a
  parallel alias owner.

Primary mathematical domain:
- conjugate saddle-functions and dual-domain support formulas in minimax theory.

Domain-style sampling used here:
- `Bifunction.lowerPairing` from `Chap07.Defn_34_2`;
- `Bifunction.lowerConjugate` from `Chap07.Definition_37_1_1`;
- `Bifunction.lowerConjugate_eq_lowerPairing_inverse_adjointFunction_of_mem_omega` from
  `Chap07.Theorem_37_1`;
- `supportFunction_effectiveDomain_convexConjugate_eq_recessionFunction` from
  `Chap03.Theorem_13_3`.

Primitive data vs derived API:
- primitive source data: the saddle-function `K`, together with the owner hypotheses
  `SaddleFunction.IsClosed K`, `K.IsConcaveConvex 𝕜`, and `K.IsProper`;
- primitive owner data reused from the chapter: `lowerConjugate K`, `dom₁ (lowerConjugate K)`,
  and `dom₂ (lowerConjugate K)`;
- derived API: the two support-function formulas of Theorem 37.2.
- ambient model layer: the theorem surface is stated at the ordered-module pairing layer used by
  nearby Chapter 34/37 owners, with codomain `WithTopBot 𝕜` and scalar-annotated relative
  interior `ri[𝕜](·)`.

Layer target: `source-facing`, but routed through the existing Chapter 34/36 owner layer instead
of a new conjugate-saddle wrapper package.
-/

/-- Theorem 37.2, `D*` formula: for a closed proper concave-convex saddle-function `K`, the
support function of the second coordinate domain `dom₂ (lowerConjugate K)` of the conjugate
saddle-function, i.e. Rockafellar's `D*`, equals the supremum over
`u ∈ ri(dom₁ K)` and `v ∈ dom₂ K` of the translation increment
`K(u, v + w) - K(u, v)`. -/
-- Proof sketch: Theorem 37.1 identifies `lowerConjugate K` with the canonical conjugate-side
-- lower representative. Its second domain is therefore the Chapter 37 `D*` domain. By Theorem
-- 34.2 this domain is the union of the effective domains of the convex slices corresponding to
-- `u ∈ ri(dom₁ K)`, while Theorem 13.3 identifies the support function of each
-- slice-domain with the recession function of the slice conjugate. The first
-- recession-function formula from
-- Theorem 8.5 then rewrites that recession function as the displayed supremum of translation
-- increments of `K`.
theorem supportFunction_conjugateDom₂_eq_iSup_iSup_translate_sub
    {K : U → XStar → WithTopBot 𝕜}
    (hK_closed : IsClosed K) (hK_proper : IsProper K)
    (hK_concaveConvex : IsConcaveConvex 𝕜 K) :
    δᵛ(· | dom₂ (lowerConjugate K)) =
      fun w : XStar ↦
        ⨆ u ∈ ri[𝕜](dom₁ K),
          ⨆ v ∈ dom₂ K, K u (v + w) - K u v := by
  let _hK_closed := hK_closed
  let _hK_proper := hK_proper
  let _hK_concaveConvex := hK_concaveConvex
  sorry

/-- Theorem 37.2, `C*` formula: for a closed proper concave-convex saddle-function `K`, the
reflected support function `z ↦ -δᵛ(-z | dom₁ (lowerConjugate K))` of the first coordinate
domain of the conjugate saddle-function, i.e. Rockafellar's `C*`, equals the infimum over
`v ∈ ri(dom₂ K)` and `u ∈ dom₁ K` of the translation increment
`K(u + z, v) - K(u, v)`. -/
-- Proof sketch: apply the preceding argument to the first coordinate domain of
-- `lowerConjugate K`, using the concave slice recovery theorem from Theorem 34.2 and the
-- sign-dual recession formula for the concave slices `u ↦ K u v`. Rewriting the support function
-- of `dom₁ (lowerConjugate K)` at `-z` produces the source expression `-δᵛ(-z | C*)`.
theorem neg_supportFunction_neg_conjugateDom₁_eq_iInf_iInf_translate_sub
    {K : U → XStar → WithTopBot 𝕜}
    (hK_closed : IsClosed K) (hK_proper : IsProper K)
    (hK_concaveConvex : IsConcaveConvex 𝕜 K) :
    (fun z : U ↦ -δᵛ(-z | dom₁ (lowerConjugate K))) =
      fun z ↦
        ⨅ v ∈ ri[𝕜](dom₂ K),
          ⨅ u ∈ dom₁ K, K (u + z) v - K u v := by
  let _hK_closed := hK_closed
  let _hK_proper := hK_proper
  let _hK_concaveConvex := hK_concaveConvex
  sorry

end

end SaddleFunction
