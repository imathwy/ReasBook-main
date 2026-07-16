import Mathlib
import StacksProject_2024.stacks_project.Chap31.Lemma_31_24_4
import StacksProject_2024.stacks_project.Chap31.Lemma_31_25_1
import StacksProject_2024.stacks_project.Chap31.Lemma_31_25_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

local notation "JX" => Opens.grothendieckTopology X.toTopCat
local notation "ModX" => ringedSiteModuleCategory JX X.toLocallyRingedSpace.𝒪
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦ Functor.IsEquivalence (tensorRight ℒ))

/- Semantic recall: `lean_leansearch` surfaced the canonical scheme assumptions
`IsIntegral`, `IsReduced`, and `IsLocallyNoetherian`; local Chapter 31 precedent supplies
`X.toLocallyRingedSpace.meromorphicSections ℒ`,
`X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s`, the finite-component hypothesis
`Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X`, and the no-embedded-points hypothesis
`X.embeddedPoints = ∅`. The Stacks tag evidence is consistent: tag `02OZ` comes from
`https://stacks.math.columbia.edu/tag/02OZ`. -/

/-- Lemma 31.25.4 (1): if `X` is an integral scheme and `\mathcal L` is an invertible
`\mathcal O_X`-module, then `\mathcal L` has a regular meromorphic section. -/
@[stacks 02OZ]
theorem exists_regularMeromorphicSection_of_isIntegral
    [IsIntegral X]
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ] :
    ∃ s : X.toLocallyRingedSpace.meromorphicSections ℒ,
      X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s := sorry

/-- Lemma 31.25.4 (2): if `X` is reduced and every quasi-compact open of `X` has finitely many
irreducible components, then every invertible `\mathcal O_X`-module has a regular meromorphic
section. -/
@[stacks 02OZ]
theorem exists_regularMeromorphicSection_of_isReduced_of_hasFiniteIrreducibleComponentsOnCompactOpens
    [IsReduced X] [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ] :
    ∃ s : X.toLocallyRingedSpace.meromorphicSections ℒ,
      X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s := sorry

/-- Lemma 31.25.4 (3): if `X` is locally Noetherian and has no embedded points, then every
invertible `\mathcal O_X`-module has a regular meromorphic section. -/
@[stacks 02OZ]
theorem exists_regularMeromorphicSection_of_isLocallyNoetherian_noEmbeddedPoints
    [IsLocallyNoetherian X]
    (hembedded : X.embeddedPoints = (∅ : Set X))
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ] :
    ∃ s : X.toLocallyRingedSpace.meromorphicSections ℒ,
      X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s := sorry

end AlgebraicGeometry
