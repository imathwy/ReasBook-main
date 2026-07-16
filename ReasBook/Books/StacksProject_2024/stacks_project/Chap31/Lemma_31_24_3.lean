import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_4_1
import StacksProject_2024.stacks_project.Chap31.Lemma_31_23_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory Opposite TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

local notation "JX" => Opens.grothendieckTopology X.toTopCat
local notation "ModX" => ringedSiteModuleCategory JX X.toLocallyRingedSpace.𝒪
local notation "MerModX" =>
  ringedSiteModuleCategory JX X.toLocallyRingedSpace.meromorphicFunctionSheaf
local notation "KX" => X.toLocallyRingedSpace.meromorphicFunctionSheaf

/- Semantic recall: `lean_leansearch` surfaced the canonical mathlib owner
`AlgebraicGeometry.IsLocallyNoetherian`. Local Chapter 31 precedent supplies
`LocallyRingedSpace.meromorphicFunctionSheaf`, the generic-point product owner from
Lemma `31.23.6`, and the source-facing no-embedded-points hypothesis
`X.embeddedPoints = ∅`. The source tag evidence is consistent: tag `0EMH` comes from
`https://stacks.math.columbia.edu/tag/0EMH`. -/

/-- Lemma 31.24.3 (1): if `X` is locally Noetherian and has no embedded points, then
the meromorphic-function sheaf `𝒦_X` is the product, equivalently the direct sum in the
source display, of the pushforwards `j_{η,*}𝒪_{X,η}` over the generic points of the
irreducible components of `X`. -/
@[stacks 0EMH]
theorem meromorphicFunctionSheaf_iso_genericPointStalkPushforwardProduct_of_isLocallyNoetherian_of_embeddedPoints_eq_empty
    (hembedded : X.embeddedPoints = (∅ : Set X)) :
    Nonempty (KX ≅ genericPointStalkPushforwardProductSheaf X) := sorry

/-- Lemma 31.24.3 (2): if `X` is locally Noetherian and has no embedded points, then
`𝒦_X` is a quasi-coherent sheaf of `𝒪_X`-algebras, recorded on the underlying
`𝒪_X`-module obtained by restriction of scalars. -/
@[stacks 0EMH]
theorem meromorphicFunctionSheaf_isQuasicoherent_of_isLocallyNoetherian_of_embeddedPoints_eq_empty
    (hembedded : X.embeddedPoints = (∅ : Set X)) :
    ((restrictionAlong
      (X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).obj
        (SheafOfModules.unit (ringSheaf JX KX) : MerModX)).IsQuasicoherent := sorry

/-- Lemma 31.24.3 (3): if `X` is locally Noetherian and has no embedded points, then for every
quasi-coherent `𝒪_X`-module `ℱ`, the meromorphic-section sheaf `𝒦_X(ℱ)` is quasi-coherent.
The displayed direct-sum/product formula over the generic points is represented by the existing
owner `X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ`. -/
@[stacks 0EMH]
theorem meromorphicSectionSheaf_isQuasicoherent_of_isLocallyNoetherian_of_embeddedPoints_eq_empty
    (hembedded : X.embeddedPoints = (∅ : Set X))
    (ℱ : ModX) [ℱ.IsQuasicoherent] :
    ((restrictionAlong
      (X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).obj
        (X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ)).IsQuasicoherent := sorry

/-- Lemma 31.24.3 (4): if `X` is locally Noetherian and has no embedded points, then the ring of
rational functions of `X` is the ring of global meromorphic functions:
`R(X) = Γ(X, 𝒦_X)`. -/
@[stacks 0EMH]
theorem rationalFunctionRing_iso_meromorphicFunctions_of_isLocallyNoetherian_of_embeddedPoints_eq_empty
    (X : Scheme)
    [IsLocallyNoetherian X]
    (hembedded : X.embeddedPoints = (∅ : Set X)) :
    Nonempty (X.rationalFunctionRing ≅ X.toLocallyRingedSpace.meromorphicFunctions) := sorry

end AlgebraicGeometry
