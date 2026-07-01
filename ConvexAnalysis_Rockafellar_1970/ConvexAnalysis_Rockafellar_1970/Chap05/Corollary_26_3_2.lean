import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_0
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_26_3

noncomputable section

open scoped Rockafellar

section

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 26.3.2 states that if `f₁` is essentially smooth, `f₂` is proper
  convex on the ambient finite-dimensional real normed space, and `ri(dom f₁⋆)` meets
  `ri(dom f₂⋆)` on the canonical dual owner, then the infimal convolution
  `f₁ □ f₂` is essentially smooth.
- `core/canonical`: the project owners already present are `Function.IsClosedProperConvex`,
  `Function.IsEssentiallySmooth`, Fenchel conjugation `f⋆`, the relative-domain notation
  `riDom(f)`, and the binary infimal convolution `f □ g`.
- `bridge/view`: this corollary is the one-step Chapter 26 consequence obtained by combining the
  essential-smooth/essential-strict-convex duality of Theorem 26.3 with the Chapter 16
  conjugate-of-sum owner and the Chapter 23 subdifferential-of-sum owner.

Domain-style sampling used here:
- `Function.IsEssentiallySmooth` from `Definition_26_1_1`;
- `Function.IsClosedProperConvex
    .isEssentiallyStrictlyConvex_iff_convexConjugate_isEssentiallySmooth`
  from `Theorem_26_3`;
- the canonical dual owner `StrongDual ℝ E` for conjugates on `NormedSpace ℝ E`;
- `riDom(·)` from `Definition_4_4`;
- the binary infimal convolution owner `f □ g` from `Text_5_4_0`.

Primitive data vs derived API:
- primitive inputs: the two functions `f₁`, `f₂`, the extra closedness hypothesis
  `LowerSemicontinuous f₁` needed to enter the Chapter 26 owner theorem on `f₁`, the essential
  smoothness hypothesis on `f₁` (which already carries convexity and properness), the
  proper-convex hypotheses on `f₂`, and the nonempty intersection
  `riDom((f₁⋆ : StrongDual ℝ E → WithBotTop ℝ)) ∩
    riDom((f₂⋆ : StrongDual ℝ E → WithBotTop ℝ))`;
- derived API: the essential smoothness of the infimal convolution `f₁ □ f₂`.

Layer target: `source-facing`, stated directly with the chapter owners rather than through a
surrogate wrapper around the dual sum `(f₁⋆ + f₂⋆)`.
-/

namespace Function.IsClosedProperConvex

variable {f₁ f₂ : E → WithBotTop ℝ}

local notation "f₁⋆ₛ" => ((f₁⋆ : StrongDual ℝ E → WithBotTop ℝ))
local notation "f₂⋆ₛ" => ((f₂⋆ : StrongDual ℝ E → WithBotTop ℝ))

/-- Corollary 26.3.2: if `f₁` is essentially smooth, `f₂` is proper convex on the ambient
finite-dimensional real normed space, and `ri(dom f₁⋆) ∩ ri(dom f₂⋆)` is nonempty on the
canonical dual owner `StrongDual ℝ E`, then the infimal convolution `f₁ □ f₂` is essentially
smooth. The Chapter 26 owner route also needs the explicit closedness hypothesis
`LowerSemicontinuous f₁` on the left input. -/
theorem
    infimal_convolution_isEssentiallySmooth_of_left_isEssentiallySmooth_of_common_riDom_conjugates
    (hclosed₁ : LowerSemicontinuous f₁) (hess₁ : f₁.IsEssentiallySmooth)
    (hf₂_convex : f₂.IsConvex ℝ) (hf₂_proper : f₂.IsProper)
    (hri : (riDom(f₁⋆ₛ) ∩ riDom(f₂⋆ₛ)).Nonempty) :
    (f₁ □ f₂).IsEssentiallySmooth := sorry

end Function.IsClosedProperConvex

end
