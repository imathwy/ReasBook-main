import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_23_7
import StacksProject_2024.stacks_project.Chap31.Lemma_31_24_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

local notation "JX" => Opens.grothendieckTopology X.toTopCat
local notation "ModX" => ringedSiteModuleCategory JX X.toLocallyRingedSpace.𝒪
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦ Functor.IsEquivalence (tensorRight ℒ))

/- Semantic recall: `lean_leansearch` surfaced the canonical mathlib owner
`AlgebraicGeometry.IsLocallyNoetherian`. Local Chapter 31 precedent supplies
`X.toLocallyRingedSpace.meromorphicSections ℒ`,
`X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s`, and the no-embedded-points hypothesis
`X.embeddedPoints = ∅`. The source tag evidence is consistent: tag `0EMI` comes from
`https://stacks.math.columbia.edu/tag/0EMI`. -/

/-- Lemma 31.24.4: if `X` is a locally Noetherian scheme with no embedded points and
`\mathcal L` is an invertible `\mathcal O_X`-module, then `\mathcal L` has a regular
meromorphic section. -/
@[stacks 0EMI]
theorem exists_regularMeromorphicSection_of_isLocallyNoetherian_of_embeddedPoints_eq_empty
    [MonoidalCategory ModX]
    (hembedded : X.embeddedPoints = (∅ : Set X))
    (ℒ : ModX) [IsInvertibleX ℒ] :
    ∃ s : X.toLocallyRingedSpace.meromorphicSections ℒ,
      X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s := sorry

end AlgebraicGeometry
