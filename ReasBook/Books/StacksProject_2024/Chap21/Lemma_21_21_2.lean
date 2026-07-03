import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.Chap18.Definition_18_19_1
import StacksProject_2024.Chap19.Lemma_19_13_6
import StacksProject_2024.Chap21.Lemma_21_20_4

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite

/-- The localized module category on a localization of a ringed site is Grothendieck abelian. -/
-- Proof sketch: the category of sheaves of modules over a sheaf of rings on a Grothendieck topos
-- is Grothendieck abelian; apply this standard fact to the localized site and its restricted
-- structure sheaf.
local instance localizationModuleCategory_isGrothendieckAbelian
    (X : RingedSite.{u, v}) (U : X) :
    IsGrothendieckAbelian.{max u v} (SheafOfModules (X.structureSheaf.over U)) := sorry

/-- Additivity of direct image from a localization into the ambient ringed site. -/
-- Proof sketch: `SheafOfModules.pushforward (SheafOfModules.pushforwardOver U)` is the
-- module-sheaf pushforward functor attached to the canonical localization morphism `j_U`;
-- pushforward of module sheaves is additive because it is induced objectwise by additive
-- restriction of scalars.
local instance localizationModuleDirectImage_additive (X : RingedSite.{u, v}) (U : X)
    [HasBinaryProducts X] :
    (SheafOfModules.pushforward (SheafOfModules.pushforwardOver U) :
      SheafOfModules (X.structureSheaf.over U) ⥤ SheafOfModules X.structureSheaf).Additive := sorry

/-- The raw source of localization direct image along `f : X ⟶ Y` identifies with
`D(\mathcal O_X)`. -/
-- Proof sketch: unfold `RingedSite.localization` and `RingedSite.Hom.ModuleDerived`; both sides
-- are definitional presentations of the same derived category of sheaves of modules on the
-- restricted structure sheaf over `X`.
theorem localizedDirectImageDerived_type_eq {Z : RingedSite.{u, v}} {X Y : Z} (f : X ⟶ Y) :
    (DerivedCategory (SheafOfModules ((Z.localization Y).structureSheaf.over (Over.mk f))) ⥤
        RingedSite.Hom.ModuleDerived (Z.localization Y)) =
      (RingedSite.Hom.ModuleDerived (Z.localization X) ⥤
        RingedSite.Hom.ModuleDerived (Z.localization Y)) := sorry

/-- In a cartesian square, restricting from `X` to `X'` and then pushing forward to `Y'` has the
same source and target categories as the textbook base-change composite. -/
-- Proof sketch: use the commutativity relation `i ≫ f = p ≫ g` from the pullback square and
-- unfold the localized structure sheaves on `X'` and `Y'`.
theorem relocalization_baseChange_type_eq
    {Z : RingedSite.{u, v}} {X' X Y' Y : Z}
    (i : X' ⟶ X) (p : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hcart : IsPullback i p f g) :
    (DerivedCategory (SheafOfModules ((Z.localization Y').structureSheaf.over (Over.mk p))) ⥤
        RingedSite.Hom.ModuleDerived (Z.localization Y')) =
      (DerivedCategory (SheafOfModules ((Z.localization X).structureSheaf.over (Over.mk i))) ⥤
        DerivedCategory (SheafOfModules ((Z.localization Y).structureSheaf.over (Over.mk g)))) :=
  sorry

/-- The unbounded derived direct-image functor attached to localization at a morphism `f : X ⟶ Y`
in a ringed site, written on the raw localized module category over `Over.mk f`. -/
private abbrev localizedDirectImageDerivedRaw {Z : RingedSite.{u, v}} {X Y : Z} (f : X ⟶ Y)
    [HasBinaryProducts (Z.localization Y)] :
    DerivedCategory (SheafOfModules ((Z.localization Y).structureSheaf.over (Over.mk f))) ⥤
      RingedSite.Hom.ModuleDerived (Z.localization Y) :=
  letI : HasBinaryProducts (Over Y) := by
    simpa [RingedSite.localization] using
      (inferInstance : HasBinaryProducts (Z.localization Y))
  let hOverStarContinuous :
      (Over.star (Over.mk f)).IsContinuous
        (Z.localization Y).siteTopology
        ((Z.localization Y).siteTopology.over (Over.mk f)) := by
    simpa [RingedSite.localization] using
      (inferInstance :
        (Over.star (Over.mk f)).IsContinuous
          (Z.siteTopology.over Y)
          ((Z.siteTopology.over Y).over (Over.mk f)))
  letI :
      (Over.star (Over.mk f)).IsContinuous
        (Z.localization Y).siteTopology
        ((Z.localization Y).siteTopology.over (Over.mk f)) :=
    hOverStarContinuous
  let φ :
      (Z.localization Y).structureSheaf ⟶
        ((Over.star (Over.mk f)).sheafPushforwardContinuous RingCat
          (Z.localization Y).siteTopology
          ((Z.localization Y).siteTopology.over (Over.mk f))).obj
          ((Z.localization Y).structureSheaf.over (Over.mk f)) :=
    SheafOfModules.pushforwardOver (Over.mk f)
  let F :
      SheafOfModules ((Z.localization Y).structureSheaf.over (Over.mk f)) ⥤
        SheafOfModules (Z.localization Y).structureSheaf :=
    @SheafOfModules.pushforward
      (Z.localization Y) _ (Over (Over.mk f)) _
      (Z.localization Y).siteTopology
      ((Z.localization Y).siteTopology.over (Over.mk f))
      (Over.star (Over.mk f))
      (Z.localization Y).structureSheaf
      ((Z.localization Y).structureSheaf.over (Over.mk f))
      hOverStarContinuous φ
  @CategoryTheory.additiveFunctorTotalRightDerived
    (SheafOfModules ((Z.localization Y).structureSheaf.over (Over.mk f)))
    (RingedSite.Hom.ModuleCat (Z.localization Y))
    _ (SheafOfModules.instAbelian ((Z.localization Y).structureSheaf.over (Over.mk f)))
    _ (SheafOfModules.instAbelian (Z.localization Y).structureSheaf)
    F
    (by
      simpa [F, φ] using
        localizationModuleDirectImage_additive (Z.localization Y) (Over.mk f))
    (localizationModuleCategory_isGrothendieckAbelian (Z.localization Y) (Over.mk f))

/-- The unbounded derived direct-image functor attached to localization at a morphism `f : X ⟶ Y`
in a ringed site. This formalizes `Rj_{X/Y,*}`. -/
private abbrev localizedDirectImageDerived {Z : RingedSite.{u, v}} {X Y : Z} (f : X ⟶ Y)
    [HasBinaryProducts (Z.localization Y)] :
    RingedSite.Hom.ModuleDerived (Z.localization X) ⥤
      RingedSite.Hom.ModuleDerived (Z.localization Y) :=
  cast (localizedDirectImageDerived_type_eq f) (localizedDirectImageDerivedRaw f)

namespace Hom

section

variable {Z : RingedSite.{u, v}} {X' X Y' Y : Z}
variable (i : X' ⟶ X) (p : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

-- Proof sketch: in this localized-ringed-site model, `j_{Y'/Y}^*` and `j_{X'/X}^*` are the exact
-- restriction functors `localizedRestrictionDerived` on the localized ringed sites `Z.localization Y`
-- and `Z.localization X`. Forgetting module structure to abelian sheaves reduces the statement to
-- Lemma `21.21.1`, and Lemma `21.20.7` identifies the two module-theoretic derived direct images
-- with the corresponding abelian ones.
/-- Lemma 21.21.2: for a ringed site `Z` and a cartesian square
`X' ⟶ X`
`↓     ↓`
`Y' ⟶ Y`, the derived direct image along localization at `f : X ⟶ Y` commutes with further
restriction to `Y'`. In the localized-ringed-site formalization, this gives a canonical
isomorphism of functors
`j_{Y'/Y}^* ∘ Rj_{X/Y,*} ≅ Rj_{X'/Y',*} ∘ j_{X'/X}^*`
from `D(\mathcal O_X)` to `D(\mathcal O_{Y'})`. -/
theorem relocalization_localizedDirectImageDerived_isomorphic
    (hcart : IsPullback i p f g)
    [HasBinaryProducts (Z.localization Y)]
    [HasBinaryProducts (Z.localization Y')]
    [(RingedSite.Hom.localizedRestriction (Z.localization Y) (Over.mk g)).Additive]
    [PreservesFiniteLimits (RingedSite.Hom.localizedRestriction (Z.localization Y) (Over.mk g))]
    [PreservesFiniteColimits
      (RingedSite.Hom.localizedRestriction (Z.localization Y) (Over.mk g))]
    [(RingedSite.Hom.localizedRestriction (Z.localization X) (Over.mk i)).Additive]
    [PreservesFiniteLimits (RingedSite.Hom.localizedRestriction (Z.localization X) (Over.mk i))]
    [PreservesFiniteColimits
      (RingedSite.Hom.localizedRestriction (Z.localization X) (Over.mk i))] :
    CategoryTheory.IsIsomorphic
      (localizedDirectImageDerived f ⋙
        RingedSite.Hom.localizedRestrictionDerived (Z.localization Y) (Over.mk g))
      (show RingedSite.Hom.ModuleDerived (Z.localization X) ⥤
          DerivedCategory (SheafOfModules ((Z.localization Y).structureSheaf.over (Over.mk g))) from
        RingedSite.Hom.localizedRestrictionDerived (Z.localization X) (Over.mk i) ⋙
          cast (relocalization_baseChange_type_eq i p f g hcart)
            (localizedDirectImageDerivedRaw p)) := sorry

end

end Hom
end RingedSite
