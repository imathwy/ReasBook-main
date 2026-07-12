import Mathlib
import StacksProject_2024.Chap31.Definition_31_14_1
import StacksProject_2024.Chap31.Definition_31_21_1
import StacksProject_2024.Chap31.Definition_31_23_7
import StacksProject_2024.Chap31.Definition_31_34_1
import StacksProject_2024.Chap31.Lemma_31_23_9
import StacksProject_2024.Chap31.Lemma_31_32_11

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced only ambient module pullback and ideal-sheaf
-- owners, so the source-faithful surface here follows local Chapter 31 precedent:
-- `RegularMeromorphicSectionIdealSheaf.idealSheaf` for denominator ideals,
-- `IsAdmissibleBlowup` for admissible blowups, and
-- `effectiveCartierDivisorDifferenceSheaf` for the source sheaf `\mathcal O(D - E)`.

variable {X X' : Scheme.{u}}

local notation "ModX" => SheafOfModules X.ringCatSheaf
local notation "ModX'" => SheafOfModules X'.ringCatSheaf
local notation "SiteModX" =>
  ringedSiteModuleCategory (Opens.grothendieckTopology X.toTopCat) X.𝒪
local notation "𝒪X'" => (SheafOfModules.unit X'.ringCatSheaf : ModX')
local notation "EffectiveCartierIdealX'" =>
  (fun I : Subobject 𝒪X' ↦
    Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I)))

/-- Helper for Lemma 31.34.6: the open complement of the support of the denominator ideal of a
regular meromorphic section. This is the source's maximal open over which the meromorphic section
is represented by an honest section. -/
abbrev denominatorRegularLocus
    [MonoidalCategory ModX] (ℒ : ModX)
    [Functor.IsEquivalence (tensorRight ℒ)]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hden : RegularMeromorphicSectionIdealSheaf ℒ s) :
    X.Opens :=
  ⟨(moduleSupport (cokernel hden.idealSheafArrow))ᶜ,
    hden.inclusionCokernel_hasClosedNowhereDenseSupport.1.isOpen_compl⟩

/-- Lemma 31.34.6 (1): if `X` is locally Noetherian, `\mathcal L` is invertible, `s` is a regular
meromorphic section of `\mathcal L`, and `b : X' ⟶ X` is the blowup in the denominator ideal of
`s`, then `b` is admissible for the maximal open on which `s` is represented by a regular section.
Here that open is formalized as `denominatorRegularLocus hden`. -/
@[stacks 0ESL]
theorem isAdmissibleBlowup_of_isBlowup_denominatorIdealSheaf
    [IsLocallyNoetherian X]
    [MonoidalCategory ModX]
    [MonoidalCategory SiteModX]
    (ℒ : ModX)
    [Functor.IsEquivalence (tensorRight ℒ)]
    [Functor.IsEquivalence (tensorRight (show SiteModX from ℒ))]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
    (hden : RegularMeromorphicSectionIdealSheaf ℒ s)
    (I : X.IdealSheafData)
    (hI : closedImmersionIdealSubobject I.subschemeι = hden.idealSheaf)
    (b : X' ⟶ X)
    [IsBlowup b I] :
    IsAdmissibleBlowup (denominatorRegularLocus ℒ s hden) b := sorry

/-- Lemma 31.34.6 (2): under the same hypotheses, after blowing up the denominator ideal of `s`
there exists an effective Cartier divisor `D` on `X'` together with an isomorphism
`b^* \mathcal L \cong \mathcal O_{X'}(D - E)`, where `E` is the exceptional divisor of the
blowup. The source's final identification of `b^* s` with `1_D \otimes (1_E)^{-1}` is recorded
through the chosen Chapter 31 owner `effectiveCartierDivisorDifferenceSheaf` for
`\mathcal O_{X'}(D - E)`. -/
@[stacks 0ESL]
theorem exists_isEffectiveCartierDivisor_and_pullbackIso_differenceSheaf_of_isBlowup_denominatorIdealSheaf
    [MonoidalCategory ModX]
    [MonoidalCategory SiteModX]
    [MonoidalCategory ModX']
    [SymmetricCategory ModX']
    [MonoidalClosed ModX']
    (ℒ : ModX)
    [Functor.IsEquivalence (tensorRight ℒ)]
    [Functor.IsEquivalence (tensorRight (show SiteModX from ℒ))]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
    (hden : RegularMeromorphicSectionIdealSheaf ℒ s)
    (I : X.IdealSheafData)
    (hI : closedImmersionIdealSubobject I.subschemeι = hden.idealSheaf)
    (b : X' ⟶ X)
    [Fact (EffectiveCartierIdealX'
      (closedImmersionIdealSubobject ((I.comap b).subschemeι)))]
    [IsBlowup b I] :
    ∃ D : X'.IdealSheafData,
      IsEffectiveCartierDivisor D ∧
        ∃ hD : Fact (EffectiveCartierIdealX'
          (closedImmersionIdealSubobject D.subschemeι)),
          Nonempty
            (((Scheme.Modules.pullback b).obj ℒ) ≅
              effectiveCartierDivisorDifferenceSheaf
                (closedImmersionIdealSubobject D.subschemeι)
                (closedImmersionIdealSubobject ((I.comap b).subschemeι))) := sorry

end AlgebraicGeometry.Scheme
