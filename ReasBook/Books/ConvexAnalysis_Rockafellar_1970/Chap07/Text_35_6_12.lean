import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Basic
import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_23_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_6_9
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_6_10
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_6_11

noncomputable section

open Function
open scoped Rockafellar

universe u v

namespace Bifunction

section Owner

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable {U : Type u} {V : Type v}
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup V] [Module 𝕜 V]
variable {Y₁ : Type*} [HasPairing U Y₁ 𝕜]
variable {Y₂ : Type*} [HasPairing V Y₂ 𝕜]
variable {K : U → V → 𝕜} {C : Set U} {D : Set V}
variable {u u' : U} {v v' : V}

local notation "Kt" => saddleExtension K C D

/-! Owner-level abstraction for Text 35.6.12:
this section keeps only the primitive bridge data needed to combine
the mixed-derivative split with the first/second partial-support identities. -/

/-- Owner form for Text 35.6.12: once the mixed directional derivative is split into the two
partial directions and each partial direction is identified with the corresponding support owner,
the mixed directional derivative is the support-sum expression. -/
theorem directionalDerivativeAt_uncurry_saddleExtension_eq_partialSubdifferentialSupportSum_owner
    (hadd :
      directionalDerivativeAt (uncurry Kt) (u, v) (u', v') =
        directionalDerivativeAt (uncurry Kt) (u, v) (u', 0) +
          directionalDerivativeAt (uncurry Kt) (u, v) (0, v'))
    (hfirst :
      directionalDerivativeAt (uncurry Kt) (u, v) (u', 0) =
        -δᵛ(-u' | ∂₁[Y₁]Kt(u, v)))
    (hsecond :
      directionalDerivativeAt (uncurry Kt) (u, v) (0, v') =
        δᵛ(v' | ∂₂[Y₂]Kt(u, v))) :
    directionalDerivativeAt (uncurry Kt) (u, v) (u', v') =
      -δᵛ(-u' | ∂₁[Y₁]Kt(u, v)) + δᵛ(v' | ∂₂[Y₂]Kt(u, v)) := sorry

/-- Inf-sup owner bridge for Text 35.6.12 at the pairing layer. -/
theorem directionalDerivativeAt_uncurry_saddleExtension_eq_iInf_iSup_subdifferentialPairing_owner
    (hsupport :
      directionalDerivativeAt (uncurry Kt) (u, v) (u', v') =
        -δᵛ(-u' | ∂₁[Y₁]Kt(u, v)) + δᵛ(v' | ∂₂[Y₂]Kt(u, v)))
    (hfirst :
      -δᵛ(-u' | ∂₁[Y₁]Kt(u, v)) =
        ⨅ uStar : ∂₁[Y₁]Kt(u, v),
          ((⟪u', (uStar : Y₁)⟫ₚ : 𝕜) : WithBotTop 𝕜))
    (hsecond :
      δᵛ(v' | ∂₂[Y₂]Kt(u, v)) =
        ⨆ vStar : ∂₂[Y₂]Kt(u, v),
          ((⟪v', (vStar : Y₂)⟫ₚ : 𝕜) : WithBotTop 𝕜)) :
    directionalDerivativeAt (uncurry Kt) (u, v) (u', v') =
      ⨅ uStar : ∂₁[Y₁]Kt(u, v),
        ⨆ vStar : ∂₂[Y₂]Kt(u, v),
          ((⟪u', (uStar : Y₁)⟫ₚ + ⟪v', (vStar : Y₂)⟫ₚ : 𝕜) : WithBotTop 𝕜) := sorry

/-- Sup-inf owner bridge for Text 35.6.12 at the pairing layer. -/
theorem directionalDerivativeAt_uncurry_saddleExtension_eq_iSup_iInf_subdifferentialPairing_owner
    (hsupport :
      directionalDerivativeAt (uncurry Kt) (u, v) (u', v') =
        -δᵛ(-u' | ∂₁[Y₁]Kt(u, v)) + δᵛ(v' | ∂₂[Y₂]Kt(u, v)))
    (hfirst :
      -δᵛ(-u' | ∂₁[Y₁]Kt(u, v)) =
        ⨅ uStar : ∂₁[Y₁]Kt(u, v),
          ((⟪u', (uStar : Y₁)⟫ₚ : 𝕜) : WithBotTop 𝕜))
    (hsecond :
      δᵛ(v' | ∂₂[Y₂]Kt(u, v)) =
        ⨆ vStar : ∂₂[Y₂]Kt(u, v),
          ((⟪v', (vStar : Y₂)⟫ₚ : 𝕜) : WithBotTop 𝕜)) :
    directionalDerivativeAt (uncurry Kt) (u, v) (u', v') =
      ⨆ vStar : ∂₂[Y₂]Kt(u, v),
        ⨅ uStar : ∂₁[Y₁]Kt(u, v),
          ((⟪u', (uStar : Y₁)⟫ₚ + ⟪v', (vStar : Y₂)⟫ₚ : 𝕜) : WithBotTop 𝕜) := sorry

end Owner

section Source

variable {U : Type u} {V : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {K : U → V → ℝ} {C : Set U} {D : Set V} {u : U} {v : V}

local notation "Kt" => saddleExtension K C D

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.12 identifies the mixed directional derivative of a finite
  concave-convex bifunction on `C ×ˢ D` with the common value of the two minimax formulas obtained
  from the first and second partial subdifferentials of its canonical ambient extension.
- `core/canonical`: the existing owner declarations are
  `SaddleFunction.IsConcaveConvexOn ℝ C D K`,
  `Bifunction.saddleExtension K C D`,
  equivalently `Function.toWithBotTopOn (uncurry K) (C ×ˢ D)`,
  `Function.directionalDerivativeAt` on `uncurry Kt`,
  `δᵛ(· | ·)`,
  `∂₁ Kt(u, v)`, and
  `∂₂ Kt(u, v)`.
- `bridge/view`: the displayed nested `iInf`/`iSup` formulas are obtained by combining the mixed
  support-function decomposition with the one-variable first-slice infimum formula and second-slice
  support-function formula. The product owner `∂ₛ Kt(u, v)` from Text 35.6.3 is not the main owner
  here: under the ordinary product pairing, `δᵛ((u', v') | ∂ₛ Kt(u, v))` computes a `sup` over the
  product, not the source minimax value.

Primary mathematical domain:
- directional derivatives and partial subdifferentials of domain-restricted concave-convex saddle
  bifunctions at interior points of product domains.

Domain-style sampling used here:
- `SaddleFunction.IsConcaveConvexOn` from `Chap07.Definition33_0_1`;
- `Bifunction.saddleExtension` from `Chap07.Definition33_0_2`;
- `Bifunction.subdifferential1At_nonempty_and_bounded_of_mem_interior_dom` and
  `Bifunction.subdifferential2At_nonempty_and_bounded_of_mem_interior_dom` from
  `Chap07.Text_35_6_9`, the chapter's canonical bridge from an interior saddle-domain hypothesis
  to nonempty partial subdifferentials;
- `Bifunction.directionalDerivativeAt_uncurry_first_eq_iInf_subdifferential1At` from
  `Chap07.Text_35_6_10`;
- `Bifunction.directionalDerivativeAt_uncurry_second_eq_supportFunction_subdifferential2At` from
  `Chap07.Text_35_6_11`;
- `Function.toWithBotTopOn` from `Chap01.Remark_4_4_5`, as the equivalent product-space
  restriction owner;
- `Function.directionalDerivativeAt` from `Chap05.Lemma_23_0_1`.

Primitive data vs derived API:
- primitive source data: a real-valued bifunction `K`, domain sets `C`, `D`, the
  concave-convex hypothesis on `C × D`, an interior base point
  `(u, v) ∈ interior (C ×ˢ D)`, and a direction pair
  `(u', v')`;
- regularity bridge data: finite-dimensional real normed structures on `U` and `V`, because in
  this project the only canonical route from the interior-domain hypothesis to the nonemptiness of
  `∂₁ Kt(u, v)` and `∂₂ Kt(u, v)` is Text 35.6.9;
- primitive owner object: the canonical ambient extension `Kt := saddleExtension K C D`, whose
  uncurried form is the same domain restriction as `Function.toWithBotTopOn (uncurry K) (C ×ˢ D)`;
- primitive owner surfaces: the mixed directional derivative of `uncurry Kt` and the two partial
  subdifferential owners `∂₁ Kt(u, v)` and `∂₂ Kt(u, v)`;
- derived API here: the additive support-function decomposition and the factorized inf-sup /
  sup-inf minimax formulas.

Layer target: `source-facing`, stated directly on the chapter's canonical mixed directional
derivative owner for the domain-restricted extension and the already-owned first/second partial
subdifferential surfaces of that same owner.

Regularity boundary:
- the displayed support/minimax formulas are not valid on arbitrary normed spaces from the present
  project API alone, because `Text_35_6_10` and `Text_35_6_11` still require finite-point and
  partial-subdifferential-nonempty hypotheses;
- keeping the source-facing interior-domain statement therefore requires staying on the
  finite-dimensional branch where Text 35.6.9 supplies those hypotheses canonically.
-/

-- Proof sketch: work on the canonical saddle extension `Kt := saddleExtension K C D`, whose
-- uncurried form is the domain-restricted ambient owner attached to `C ×ˢ D`. Split the mixed
-- directional derivative into the two partial directions on that owner, then apply Texts 35.6.10
-- and 35.6.11 to rewrite the first summand as `-δᵛ(-u' | ∂₁ Kt(u, v))` and the second as
-- `δᵛ(v' | ∂₂ Kt(u, v))`.
/-- Text 35.6.12, owner form: on the finite-dimensional real normed-space branch, at an interior
point `(u, v)` of a concave-convex product domain, the mixed directional derivative of the
canonical saddle extension is the sum of the support owners attached to the first and second
partial subdifferentials of that extension. -/
theorem directionalDerivativeAt_uncurry_saddleExtension_eq_partialSubdifferentialSupportSum
    (hK_concaveConvex : SaddleFunction.IsConcaveConvexOn ℝ C D K)
    (huv : (u, v) ∈ interior (C ×ˢ D))
    (u' : U) (v' : V) :
    directionalDerivativeAt (uncurry Kt) (u, v) (u', v') =
      -δᵛ(-u' | ∂₁ Kt(u, v)) + δᵛ(v' | ∂₂ Kt(u, v)) := sorry

-- Proof sketch: combine the owner theorem above with the Chapter 13 support-function/infimum
-- bridge for the first term, still on the same saddle-extension owner.
/-- Text 35.6.12, source-facing bridge form: on the same finite-dimensional branch, the same mixed
directional-derivative value can be written as the corresponding inf-sup over the two partial
subdifferentials. -/
theorem directionalDerivativeAt_uncurry_saddleExtension_eq_iInf_iSup_subdifferentialPairing
    (hK_concaveConvex : SaddleFunction.IsConcaveConvexOn ℝ C D K)
    (huv : (u, v) ∈ interior (C ×ˢ D))
    (u' : U) (v' : V) :
    directionalDerivativeAt (uncurry Kt) (u, v) (u', v') =
      ⨅ uStar : ∂₁ Kt(u, v),
        ⨆ vStar : ∂₂ Kt(u, v),
          ((⟪u', (uStar : StrongDual ℝ U)⟫ₚ +
            ⟪v', (vStar : StrongDual ℝ V)⟫ₚ : ℝ) : WithBotTop ℝ) := sorry

-- Proof sketch: this is the symmetric bridge view of the same minimax value.
/-- On the same finite-dimensional branch, the mixed directional-derivative value can equally be
written as the corresponding sup-inf over the two partial subdifferentials. -/
theorem directionalDerivativeAt_uncurry_saddleExtension_eq_iSup_iInf_subdifferentialPairing
    (hK_concaveConvex : SaddleFunction.IsConcaveConvexOn ℝ C D K)
    (huv : (u, v) ∈ interior (C ×ˢ D))
    (u' : U) (v' : V) :
    directionalDerivativeAt (uncurry Kt) (u, v) (u', v') =
      ⨆ vStar : ∂₂ Kt(u, v),
        ⨅ uStar : ∂₁ Kt(u, v),
          ((⟪u', (uStar : StrongDual ℝ U)⟫ₚ +
            ⟪v', (vStar : StrongDual ℝ V)⟫ₚ : ℝ) : WithBotTop ℝ) := sorry

end Source

end Bifunction
