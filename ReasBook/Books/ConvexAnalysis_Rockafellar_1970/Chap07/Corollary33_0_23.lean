import ConvexAnalysis_Rockafellar_1970.Chap07.Lemma33_0_22

noncomputable section

universe u v w z

open scoped Rockafellar

namespace Bifunction

section

variable {𝕜 : Type z} {U : Type u} {X : Type v} {XStar : Type w}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable [TopologicalSpace U] [AddCommMonoid U] [Module 𝕜 U]
variable [TopologicalSpace X] [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid XStar] [Module 𝕜 XStar]
variable [HasLinearPairing X XStar 𝕜]

-- Proof sketch: apply `lowerPairing_isConcaveConvex_of_uncurry_isConvex` to the convexity field
-- of `hF`, and apply `lowerPairing_isConcaveClosed_of_isClosedConvex` to `F`, `hF`, and `hpair`.
/-- Corollary33.0.23: if `F` is closed convex and the pairing slices
`x ↦ (⟪x, x⋆⟫ₚ : WithTopBot 𝕜)` are lower semicontinuous, then the lower representative
`(u, x⋆) ↦ (F u)⋆ x⋆` is concave in `u`, convex in `x⋆`, and closed concave in `u`. -/
namespace IsClosedConvex

theorem lowerPairing_isConcaveConvex_and_isConcaveClosed
    {F : U → X → WithTopBot 𝕜} (hF : IsClosedConvex F)
    (hpair : ∀ xStar : XStar,
      LowerSemicontinuous (fun x : X ↦ (⟪x, xStar⟫ₚ : WithTopBot 𝕜))) :
    IsConcaveConvex 𝕜 (lowerPairing XStar F) ∧
      IsConcaveClosed (lowerPairing XStar F) := by
  refine ⟨?_, ?_⟩
  · exact lowerPairing_isConcaveConvex_of_uncurry_isConvex F hF.convex
  · exact lowerPairing_isConcaveClosed_of_isClosedConvex F hF hpair

end IsClosedConvex

end

end Bifunction
