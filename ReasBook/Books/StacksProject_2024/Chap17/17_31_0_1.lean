import Mathlib
import StacksProject_2024.Chap18.«18_35_0_2»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits TopCat
open SheafOfModules.RingedSite

universe u

noncomputable section

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [Limits.HasBinaryCoproducts (TopCat.Sheaf CommRingCat.{u} X)]
variable (𝒜 : TopCat.Sheaf CommRingCat.{u} X) (𝒝 : Under 𝒜)

local notation "JX" => Opens.grothendieckTopology X

private instance topCatSheaf_hasBinaryCoproducts :
    HasBinaryCoproducts (CategoryTheory.Sheaf JX CommRingCat.{u}) := by
  simpa [TopCat.Sheaf] using
    (inferInstance : HasBinaryCoproducts (TopCat.Sheaf CommRingCat.{u} X))

/- Domain-style sampling for 17.31.0.1:
- primary domain: the canonical polynomial presentation `\mathcal A[\mathcal B] \to \mathcal B`
  of a sheaf of `\mathcal A`-algebras on the opens site of `X`;
- sampled owner declarations:
  `SheafOfModules.RingedSite.presentationVariables`,
  `SheafOfModules.RingedSite.presentationFreeSheaf`,
  `SheafOfModules.RingedSite.presentationMap`,
  `Under.costarAdjForget`;
- best owner abstraction: the chapter already owns the presentation data at the generic site level
  in `SheafOfModules.RingedSite`, so this file should keep only the opens-site specialization and
  the source-facing bracket companion theorem;
- primitive data: the imported site-level presentation owners specialized to `JX`;
- derived API: only the bracket formula saying that the canonical presentation map sends the
  generator `[b]` to `b`.

Source/core/bridge triage:
- `source-facing`: `presentationMap_on_brackets`;
- `core/canonical`: the site-level owners
  `presentationVariables`, `presentationFreeSheaf`, `presentationBase`, and `presentationMap`;
- `bridge/view`: this file is only the opens-site specialization of those owners. -/

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
  [Limits.HasBinaryCoproducts (TopCat.Sheaf CommRingCat.{u} X)] in
private theorem presentationFreeMap_on_brackets
    (𝒜 : TopCat.Sheaf CommRingCat.{u} X)
    (𝒝 : Under 𝒜) :
    (CategoryTheory.Sheaf.adjunction JX CommRingCat.adj).unit.app
        (presentationVariables 𝒝) ≫
      (CategoryTheory.sheafForget JX).map
        (presentationFreeMap 𝒝 (presentationVariables 𝒝) (𝟙 _)) =
      𝟙 (presentationVariables 𝒝) := by
  simpa [Adjunction.homEquiv_unit] using
    (Equiv.apply_symm_apply
      ((CategoryTheory.Sheaf.adjunction JX CommRingCat.adj).homEquiv
        (presentationVariables 𝒝) 𝒝.right)
      (𝟙 (presentationVariables 𝒝)))

/- Source-facing specialization: in the canonical presentation
`\mathcal A[\mathcal B] \to \mathcal B`, the bracket generator `[b]` maps to `b`. -/
omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
theorem presentationMap_on_brackets :
    (CategoryTheory.Sheaf.adjunction JX CommRingCat.adj).unit.app
        (presentationVariables 𝒝) ≫
      (CategoryTheory.sheafForget JX).map
        ((Under.costarAdjForget 𝒜).unit.app
            (presentationFreeSheaf (presentationVariables 𝒝)) ≫
          presentationMap 𝒜 𝒝) =
      𝟙 (presentationVariables 𝒝) := by
  have hbracket :
      (Under.costarAdjForget 𝒜).unit.app
          (presentationFreeSheaf (presentationVariables 𝒝)) ≫
        presentationMap 𝒜 𝒝 =
      presentationFreeMap 𝒝 (presentationVariables 𝒝) (𝟙 _) := by
    let e := (Under.costarAdjForget 𝒜).homEquiv
      (presentationFreeSheaf (presentationVariables 𝒝)) 𝒝
    simpa [presentationMap, presentationMapOf, Adjunction.homEquiv_unit] using
      (Equiv.apply_symm_apply e
        (presentationFreeMap 𝒝 (presentationVariables 𝒝) (𝟙 _)))
  have hforget :
      (CategoryTheory.Sheaf.adjunction JX CommRingCat.adj).unit.app
          (presentationVariables 𝒝) ≫
        (CategoryTheory.sheafForget JX).map
          ((Under.costarAdjForget 𝒜).unit.app
              (presentationFreeSheaf (presentationVariables 𝒝)) ≫
            presentationMap 𝒜 𝒝) =
      (CategoryTheory.Sheaf.adjunction JX CommRingCat.adj).unit.app
          (presentationVariables 𝒝) ≫
        (CategoryTheory.sheafForget JX).map
          (presentationFreeMap 𝒝 (presentationVariables 𝒝) (𝟙 _)) := by
    exact congrArg
      (fun f ↦
        (CategoryTheory.Sheaf.adjunction JX CommRingCat.adj).unit.app
            (presentationVariables 𝒝) ≫
          (CategoryTheory.sheafForget JX).map f)
      hbracket
  calc
    (CategoryTheory.Sheaf.adjunction JX CommRingCat.adj).unit.app
        (presentationVariables 𝒝) ≫
      (CategoryTheory.sheafForget JX).map
        ((Under.costarAdjForget 𝒜).unit.app
          (presentationFreeSheaf (presentationVariables 𝒝)) ≫
          presentationMap 𝒜 𝒝) =
      (CategoryTheory.Sheaf.adjunction JX CommRingCat.adj).unit.app
          (presentationVariables 𝒝) ≫
        (CategoryTheory.sheafForget JX).map
          (presentationFreeMap 𝒝 (presentationVariables 𝒝) (𝟙 _)) := hforget
    _ = 𝟙 (presentationVariables 𝒝) := presentationFreeMap_on_brackets 𝒜 𝒝

end TopCat.Sheaf
