import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on the ringed site
`(\mathcal C, \mathcal O)`. -/
private abbrev ringedSiteModules :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- Restriction of `\mathcal O`-modules from `(\mathcal C, \mathcal O)` to the localized
ringed site `(\mathcal C/U, \mathcal O_U)`. -/
private abbrev localizedRestriction :
    ringedSiteModules J 𝒪 ⥤
      SheafOfModules (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U) :=
  SheafOfModules.pushforward (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))

variable [(localizedRestriction J 𝒪 U).PreservesZeroMorphisms]

-- Proof sketch: the localization restriction functor `j_U^*` on `\mathcal O`-modules is right
-- adjoint to extension by zero `j_{U!}` by the canonical localized adjunction, and
-- `j_{U!}` is exact by Lemma `18.19.3`. Apply Lemma `13.31.9` to conclude that the induced
-- functor on cochain complexes preserves K-injective complexes.
/-- Lemma 21.20.1: for a ringed site `(\mathcal C, \mathcal O)`, an object `U : \mathcal C`, and
a K-injective complex of `\mathcal O`-modules, the restricted complex on the localized ringed site
`(\mathcal C/U, \mathcal O_U)` is K-injective. -/
theorem ringedSiteLocalizedRestriction_isKInjective
    (I : CochainComplex (ringedSiteModules J 𝒪) ℤ) [I.IsKInjective] :
    let K := (((localizedRestriction J 𝒪 U).mapHomologicalComplex (up ℤ)).obj I)
    CochainComplex.IsKInjective K :=
  sorry

end
