import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]

private abbrev localizedRestriction
    (𝒪 : Sheaf J RingCat.{w}) (U : C) :
    SheafOfModules 𝒪 ⥤ SheafOfModules (𝒪.over U) :=
  SheafOfModules.pushforward (𝟙 (𝒪.over U))

-- Proof sketch: restriction to the localized ringed site is right adjoint to extension by zero,
-- and extension by zero is exact; apply the standard adjunction criterion that a right adjoint to
-- an exact functor preserves injective objects.
/-- Lemma 21.7.1 (1): if `ℐ` is an injective `\mathcal O`-module on a ringed site
`(\mathcal C, \mathcal O)`, then its restriction to the localized ringed site
`(\mathcal C/U, \mathcal O_U)` is an injective `\mathcal O_U`-module. -/
theorem ringedSite_localizationModuleRestriction_injective
    (𝒪 : Sheaf J RingCat.{w}) (U : C) (ℐ : SheafOfModules 𝒪)
    (hℐ : Injective ℐ) :
    Injective ((localizedRestriction 𝒪 U).obj ℐ) := sorry

-- Proof sketch: choose an injective resolution of `ℱ` in `Mod(\mathcal O)`, restrict it to the
-- localized ringed site using part (1), and compute both sides by the homology of the same
-- sections complex; sections of `ℱ` over `U` agree with global sections of `ℱ|_U` on `X/U`.
/-- Lemma 21.7.1 (2): for an `\mathcal O`-module `ℱ` on a ringed site
`(\mathcal C, \mathcal O)` and an object `U : \mathcal C`, the cohomology of `ℱ` over `U`
agrees with the cohomology of the restricted module on the localized ringed site
`(\mathcal C/U, \mathcal O_U)`. -/
theorem ringedSite_localizationModuleRestriction_cohomologyOver_eq
    (𝒪 : Sheaf J RingCat.{w}) (U : C)
    [HasSheafify J AddCommGrpCat]
    [HasExt (Sheaf J AddCommGrpCat)]
    [HasSheafify (J.over U) AddCommGrpCat]
    [HasExt (Sheaf (J.over U) AddCommGrpCat)]
    (ℱ : SheafOfModules 𝒪) (p : ℕ) :
    (((SheafOfModules.toSheaf 𝒪).obj ℱ).H' p U) =
      AddCommGrpCat.of
        (((SheafOfModules.toSheaf (𝒪.over U)).obj
          ((localizedRestriction 𝒪 U).obj ℱ)).H p) := sorry
