import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_3
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_37_1_1

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
