import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_1_3
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_16_4_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_8
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_0_1

noncomputable section

open scoped BigOperators Rockafellar

namespace Bifunction

section Owner

universe u v

variable {U : Type u} {X : Type v} {α : Type*}
variable [Preorder α]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 38.1 studies the infimal-convolution sum `F₁ D F₂` of two convex
  bifunctions, defined fiberwise in the second variable, together with its domain and lower-pairing
  formulas.
- `core/canonical`: the owner abstraction for the bifunction operation already appears upstream in
  `Chap08.Definition_38_0_1` as `Bifunction.infimalConvolution`, written `D`, while the
  slice-domain owner `Bifunction.dom` already appears upstream in
  `Chap06.Definition_6_29_8`.
- `bridge/view`: the slice-domain owner `dom` is the exact source notion “the parameter values
  where the slice is proper”; the bifunction infimal-convolution owner itself is reused directly
  from `Definition_38_0_1`, whose implementation is the canonical slice-level owner expression
  `fun u ↦ F₁ u □ F₂ u`.

Domain-style sampling used here:
- `Bifunction.infimalConvolution`, the notation `D`, and
  `Bifunction.uncurry_infimalConvolution` from `Chap08.Definition_38_0_1`;
- `Function.IsProper` from `Chap01.Definition_4_6`;
- `Function.IsConvex.infimal_convolution` from `Chap01.Theorem_5_4`;
- `infimal_convolution_dom_eq_add_of_isProper` from `Chap01.Text_5_4_1_3`;
- `Bifunction.lowerPairing` from `Chap07.Defn_34_2`;
- `convexConjugate_finiteInfimalConvolution_eq_sum` from
  `Chap03.Theorem_16_4_1`.

Primitive data vs derived API:
- primitive source-facing slice-domain owner: the existing `Bifunction.dom`;
- derived API: the bifunction properness owner `Bifunction.IsProper = (dom F).Nonempty`, graph
  convexity of the new bifunction, the domain intersection theorem, and the lower-pairing
  addition theorem.

Layer target:
- `source-facing` for `dom` and the theorem statements about `D`;
- `bridge/view` through the upstream owner `Bifunction.infimalConvolution`.
-/

/-- A bifunction is proper when its slice-domain is nonempty. This is the chapter-level
source-facing properness owner built directly from `dom`. -/
def IsProper (F : U → X → WithBotTop α) : Prop :=
  (dom F).Nonempty

end Owner

section Theorem

universe u v

variable {U : Type u} {X : Type v} {𝕜 : Type*}

section Convexity

variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [DenselyOrdered 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

-- Proof sketch: rewrite `Function.uncurry (F₁ D F₂)` with
-- `uncurry_infimalConvolution`. Convexity of the graph function then follows from the same
-- partial-infimal-convolution convexity mechanism that underlies the one-variable theorem for
-- `□`, applied on `U × X`.
/-- Theorem 38.1, convexity clause: the infimal convolution of two convex bifunctions is again a
convex bifunction, expressed in the chapter owner language as convexity of the uncurried graph
function of `F₁ D F₂`. -/
theorem uncurry_infimalConvolution_isConvex
    {F₁ F₂ : U → X → WithBotTop 𝕜}
    (hF₁ : (Function.uncurry F₁).IsConvex 𝕜)
    (hF₂ : (Function.uncurry F₂).IsConvex 𝕜) :
    (Function.uncurry (F₁ D F₂)).IsConvex 𝕜 := by
  sorry

end Convexity

section Domain

variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [DenselyOrdered 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]

-- Proof sketch: for each fixed parameter `u`, the slice of `F₁ D F₂` is the ordinary infimal
-- convolution `(F₁ u) □ (F₂ u)`. The owner theorem
-- `infimal_convolution_dom_eq_add_of_isProper` identifies its effective domain as
-- `dom(F₁ u) + dom(F₂ u)`, so the right-to-left implication is the direct nonempty-Minkowski-sum
-- consequence. The reverse implication uses the convex-slice hypotheses to rule out the improper
-- `⊥`-valued pathology once the infimal-convolution slice is proper.
/-- Theorem 38.1, domain clause: the slice-domain of the bifunction infimal convolution is the
intersection of the two slice-domains. -/
theorem dom_infimalConvolution_eq_inter
    {F₁ F₂ : U → X → WithBotTop 𝕜}
    (hF₁_convex : ∀ u, (F₁ u).IsConvex 𝕜)
    (hF₂_convex : ∀ u, (F₂ u).IsConvex 𝕜) :
    dom (F₁ D F₂) = dom F₁ ∩ dom F₂ := by
  sorry

end Domain

section LowerPairing

variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [HasLinearPairing X X 𝕜]

-- Proof sketch: for each fixed `u`, rewrite the slice `(F₁ D F₂) u` as the binary infimal
-- convolution `(F₁ u) □ (F₂ u)`, apply the two-term specialization of
-- `convexConjugate_finiteInfimalConvolution_eq_sum`, and then curry back to the Chapter
-- 34 owner `lowerPairing`. The source properness wording is a thin companion specialization,
-- because the owner-level conjugacy theorem only uses pointwise exclusion of `⊥`.
/-- Theorem 38.1, lower-pairing clause: the lower representative of the bifunction infimal
convolution is the pointwise sum of the lower representatives of the two factors. This is the
source formula `⟪(F₁ D F₂)ᵤ, x⋆⟫ = ⟪F₁ᵤ, x⋆⟫ + ⟪F₂ᵤ, x⋆⟫`, stated with the minimal owner-side
no-`⊥` hypothesis needed upstream. -/
theorem lowerPairing_infimalConvolution_eq_add
    {F₁ F₂ : U → X → WithBotTop 𝕜}
    (hF₁_ne_bot : ∀ u x, F₁ u x ≠ ⊥)
    (hF₂_ne_bot : ∀ u x, F₂ u x ≠ ⊥) :
    lowerPairing (XStar := X) (F₁ D F₂) =
      lowerPairing (XStar := X) F₁ + lowerPairing (XStar := X) F₂ := by
  ext u xStar
  let f : Fin 2 → X → WithBotTop 𝕜 := ![F₁ u, F₂ u]
  have hf_ne_bot : ∀ i x, f i x ≠ ⊥ := by
    intro i x
    fin_cases i <;> simp [f, hF₁_ne_bot, hF₂_ne_bot]
  change ((F₁ u □ F₂ u)⋆ : X → WithBotTop 𝕜) xStar = _
  rw [show F₁ u □ F₂ u = finiteInfimalConvolution f by
        simpa [f] using (finiteInfimalConvolution_two_eq_infimal_convolution f).symm]
  simpa [f, Fin.sum_univ_two, Pi.add_apply] using
    congrFun (convexConjugate_finiteInfimalConvolution_eq_sum f hf_ne_bot) xStar

/-- Properness-form specialization of the lower-pairing clause. This companion adds no new
mathematics: it only repackages the owner-side no-`⊥` hypothesis via `Function.IsProper.ne_bot`. -/
theorem lowerPairing_infimalConvolution_eq_add_of_proper
    {F₁ F₂ : U → X → WithBotTop 𝕜}
    (hF₁_proper : ∀ u, (F₁ u).IsProper)
    (hF₂_proper : ∀ u, (F₂ u).IsProper) :
    lowerPairing (XStar := X) (F₁ D F₂) =
      lowerPairing (XStar := X) F₁ + lowerPairing (XStar := X) F₂ := by
  exact lowerPairing_infimalConvolution_eq_add
    (fun u x ↦ (hF₁_proper u).ne_bot x)
    (fun u x ↦ (hF₂_proper u).ne_bot x)

end LowerPairing

end Theorem

end Bifunction
