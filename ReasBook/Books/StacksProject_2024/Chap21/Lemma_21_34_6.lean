import Mathlib
import StacksProject_2024.Chap18.Definition_18_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

universe u v

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
private abbrev RingedSiteModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The abelian category `\mathrm{Mod}(\mathcal O_U)` on the localized ringed site
`X.localization U`. -/
private abbrev LocalizedRingedSiteModuleCat (X : RingedSite.{u, v}) (U : X) :=
  SheafOfModules (X.structureSheaf.over U)

/-- Restriction of `\mathcal O_X`-modules to the localized ringed site `X.localization U`. -/
private abbrev localizedRestrictionFunctor (X : RingedSite.{u, v}) (U : X) :
    RingedSiteModuleCat X ⥤ LocalizedRingedSiteModuleCat X U :=
  SheafOfModules.pushforward (𝟙 (X.structureSheaf.over U))

/-- Restriction of a cochain complex of `\mathcal O_X`-modules to the localized ringed site
`X.localization U`. -/
private abbrev localizedRestrictionComplex (X : RingedSite.{u, v}) (U : X)
    [(localizedRestrictionFunctor X U).PreservesZeroMorphisms] :
    CochainComplex (RingedSiteModuleCat X) ℤ →
      CochainComplex (LocalizedRingedSiteModuleCat X U) ℤ :=
  fun K ↦ ((localizedRestrictionFunctor X U).mapHomologicalComplex (up ℤ)).obj K

section

variable (X : RingedSite.{u, v})

local notation "ModX" => RingedSiteModuleCat X

/-- The derived-category object of `D(\mathcal O_X)` represented by a cochain complex of
`\mathcal O_X`-modules. -/
private abbrev ambientDerivedObject
    [HasDerivedCategory ModX] :
    CochainComplex ModX ℤ → DerivedCategory ModX :=
  fun K ↦ DerivedCategory.Q.obj K

/-- The homotopy-category object represented by a cochain complex of `\mathcal O_X`-modules. -/
private abbrev ambientHomotopyObject :
    CochainComplex ModX ℤ → HomotopyCategory ModX (up ℤ) :=
  fun K ↦ (HomotopyCategory.quotient ModX (up ℤ)).obj K

/-- The derived-category object of `D(\mathcal O_U)` represented by the restriction of a cochain
complex of `\mathcal O_X`-modules to `X.localization U`. -/
private abbrev localizedDerivedObject (U : X)
    [HasDerivedCategory (LocalizedRingedSiteModuleCat X U)]
    [(localizedRestrictionFunctor X U).PreservesZeroMorphisms] :
    CochainComplex ModX ℤ →
      DerivedCategory (LocalizedRingedSiteModuleCat X U) :=
  fun K ↦ DerivedCategory.Q.obj (localizedRestrictionComplex X U K)

/-- The homotopy-category object represented by the restriction of a cochain complex of
`\mathcal O_X`-modules to `X.localization U`. -/
private abbrev localizedHomotopyObject (U : X)
    [(localizedRestrictionFunctor X U).PreservesZeroMorphisms] :
    CochainComplex ModX ℤ →
      HomotopyCategory (LocalizedRingedSiteModuleCat X U) (up ℤ) :=
  fun K ↦
    (HomotopyCategory.quotient (LocalizedRingedSiteModuleCat X U) (up ℤ)).obj
      (localizedRestrictionComplex X U K)

-- Proof sketch: first identify the degree-zero cohomology of the localized Hom complex with
-- morphisms in the localized homotopy category via `21.34.0.1`. Then apply Lemma `21.20.1` to
-- see that the restricted target complex remains K-injective, so the localization functor
-- `K(\mathcal O_U) ⥤ D(\mathcal O_U)` is bijective on morphisms into it.
/-- Lemma 21.34.6 (1): for a ringed site `(\mathcal C, \mathcal O)`, an object `U : \mathcal C`,
a complex `\mathcal L^\bullet` of `\mathcal O`-modules, and a K-injective complex
`\mathcal I^\bullet` of `\mathcal O`-modules, the localization functor
`K(\mathcal O_U) \to D(\mathcal O_U)` is bijective on morphisms from
`\mathcal L^\bullet|_U` to `\mathcal I^\bullet|_U`. Combined with `21.34.0.1`, this is the
textbook equality
`\operatorname{H}^0(\Gamma(U,\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet,\mathcal I^\bullet)))
= \operatorname{Hom}_{D(\mathcal O_U)}(L|_U, M|_U)`. -/
theorem localized_internalHom_h0_qh_map_bijective
    (U : X)
    [HasDerivedCategory (LocalizedRingedSiteModuleCat X U)]
    [(localizedRestrictionFunctor X U).PreservesZeroMorphisms]
    (L I : CochainComplex ModX ℤ)
    [I.IsKInjective] :
    Function.Bijective
      (DerivedCategory.Qh.map :
        (localizedHomotopyObject X U L ⟶ localizedHomotopyObject X U I) →
          (localizedDerivedObject X U L ⟶ localizedDerivedObject X U I)) := sorry

-- Proof sketch: identify `H^0` of the Hom complex with morphisms in the homotopy category by
-- `21.34.0.2`, and then use the standard fact that a K-injective target computes morphisms in the
-- derived category because `DerivedCategory.Qh.map` is bijective on morphisms into a K-injective
-- complex.
/-- Lemma 21.34.6 (2): for a ringed site `(\mathcal C, \mathcal O)`, a complex
`\mathcal L^\bullet` of `\mathcal O`-modules, and a K-injective complex
`\mathcal I^\bullet` of `\mathcal O`-modules, the localization functor
`K(\mathcal O) \to D(\mathcal O)` is bijective on morphisms from `\mathcal L^\bullet` to
`\mathcal I^\bullet`. Combined with `21.34.0.2`, this is the textbook equality
`\operatorname{H}^0(\Gamma(\mathcal C,\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet,
\mathcal I^\bullet))) = \operatorname{Hom}_{D(\mathcal O)}(L, M)`. -/
theorem internalHom_h0_qh_map_bijective
    [HasDerivedCategory ModX]
    (L I : CochainComplex ModX ℤ)
    [I.IsKInjective] :
    Function.Bijective
      (DerivedCategory.Qh.map :
        (ambientHomotopyObject X L ⟶ ambientHomotopyObject X I) →
          (ambientDerivedObject X L ⟶ ambientDerivedObject X I)) := sorry

end
