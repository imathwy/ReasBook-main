import ConvexAnalysis_Rockafellar_1970.Chap07.Lemma33_0_18

noncomputable section

universe u v w z

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Theorem33.0.16 says that Chapter 33 admissible convex bifunctions and
  admissible concave-convex kernels are exactly related by partial Fenchel conjugation in the
  second variable.
- `core/canonical`: this owner layer is already formalized by
  `Bifunction.lowerPairingSourceAdmissible`, `Bifunction.lowerPairingTargetAdmissible`, and the
  inverse-on-classes bridge `Bifunction.lowerPairing_invOn_admissibleClasses`.
- `bridge/view`: this file keeps the source theorem name while presenting the class surfaces via
  those canonical owner predicates instead of expanded raw conjunctions.

Layer target: `bridge/view`.
-/

section

variable {𝕜 : Type z} {U : Type u} {X : Type v} {XStar : Type w}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [OrderTopology 𝕜] [NoBotOrder 𝕜] [NoMinOrder 𝕜] [Nonempty 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X] [FiniteDimensional 𝕜 X]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [FiniteDimensional 𝕜 XStar]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]
variable [HasLinearPairing XStar X 𝕜] [HasContinuousPairing XStar X 𝕜]

/-- Theorem33.0.16: partial Fenchel conjugation in the second variable is inverse, on the class
of admissible convex bifunctions and the class of admissible concave-convex kernels, to the
reverse partial Fenchel conjugation. -/
theorem partialConjugation_invOn_convexLowerSemicontinuous_classes :
    Set.InvOn
      (lowerPairing X)
      (lowerPairing XStar)
      {F : U → X → WithTopBot 𝕜 | lowerPairingSourceAdmissible F}
      {K : U → XStar → WithTopBot 𝕜 | lowerPairingTargetAdmissible K} := by
  simpa using
    (lowerPairing_invOn_admissibleClasses
      (𝕜 := 𝕜) (U := U) (X := X) (XStar := XStar))

end

end Bifunction
