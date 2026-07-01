import ConvexAnalysis_Rockafellar_1970.Chap07.Lemma33_0_18

noncomputable section

universe u v w z

open scoped Rockafellar

namespace Bifunction

section Corollary33_1_2

variable {𝕜 : Type z} {U : Type u} {X : Type v} {XStar : Type w}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsOrderedAddMonoid 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]
variable [HasLinearPairing XStar X 𝕜] [HasContinuousPairing XStar X 𝕜]

-- Canonical source/target admissible classes for the partial-conjugation correspondence.
local notation "SrcClass" => {F | lowerPairingSourceAdmissible F}
local notation "TgtClass" => {K | lowerPairingTargetAdmissible K}

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 33.1.2 is the one-to-one correspondence between convex bifunctions
  closed in the second variable and concave-convex kernels closed in the second variable.
- `core/canonical`: the owner ingredients are the forward/reverse theorem-level constructions from
  `Theorem33_1` together with the inverse-on-classes theorem
  `lowerPairing_invOn_admissibleClasses`.
- `bridge/view`: this file packages those ingredients into the closed-class `Set.BijOn`
  correspondence, which is exactly the corollary layer and not the main theorem layer.

Primary mathematical domain:
- partial Fenchel conjugation of bifunction slices and its closed-class correspondence.

Domain-style sampling used here:
- `lowerPairing`;
- `lowerPairing_isConcaveConvex_of_uncurry_isConvex`;
- `lowerPairing_isConvexClosed`;
- `lowerPairing_uncurry_isConvex_of_isConcaveConvex`;
- `lowerPairing_invOn_admissibleClasses`.

Primitive data vs derived API:
- primitive owners: `lowerPairing`, graph convexity, second-variable closedness, and saddle
  concave-convexity;
- derived API: the `Set.BijOn` correspondence theorem below, under the pairing-slice
  lower-semicontinuity hypotheses used by `Theorem33_1`.

Layer target: `source-facing`.
-/

/-- Corollary33.1.2: partial Fenchel conjugation in the second variable gives a one-to-one
correspondence between convex bifunctions closed in the second variable and concave-convex kernels
closed in the second variable, provided the pairing slices are lower semicontinuous in the dual
variable for both pairing orientations. -/
theorem lowerPairing_bijOn_admissibleClasses
    (hpair :
      ∀ x : X, LowerSemicontinuous (fun xStar : XStar ↦ ⟪x, xStar⟫ₚ))
    (hpair' :
      ∀ xStar : XStar, LowerSemicontinuous (fun x : X ↦ ⟪xStar, x⟫ₚ)) :
    Set.BijOn
      (lowerPairing XStar)
      SrcClass
      TgtClass := by
  refine lowerPairing_invOn_admissibleClasses.bijOn ?_ ?_
  · intro F hF
    exact ⟨
      lowerPairing_isConcaveConvex_of_uncurry_isConvex F hF.1,
      lowerPairing_isConvexClosed F hpair
    ⟩
  · intro K hK
    exact ⟨
      lowerPairing_uncurry_isConvex_of_isConcaveConvex K hK.1,
      lowerPairing_isConvexClosed K hpair'
    ⟩

end Corollary33_1_2

end Bifunction
