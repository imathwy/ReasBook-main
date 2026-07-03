import Mathlib
import stacks_project.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
    (CategoryTheory.forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The structure-sheaf morphism `\mathcal O_Y ⟶ f_* \mathcal O_X` attached to a morphism of
ringed spaces. -/
noncomputable abbrev ringedSpaceCommRingSheafPushforwardMap
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf :=
  ⟨f.hom.c⟩

/-- The structure-sheaf morphism of a morphism of ringed spaces after forgetting commutativity. -/
noncomputable abbrev ringedSpacePushforwardStructureSheafHom
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    ringedSpaceRingCatSheaf Y ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (ringedSpaceRingCatSheaf X) :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology Y)
    (CategoryTheory.forget₂ CommRingCat RingCat.{u})).map
      (ringedSpaceCommRingSheafPushforwardMap f)

/-- The direct-image functor on `\mathcal O_X`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev ringedSpaceModulePushforward
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    SheafOfModules (ringedSpaceRingCatSheaf X) ⥤
      SheafOfModules (ringedSpaceRingCatSheaf Y) :=
  SheafOfModules.pushforward (ringedSpacePushforwardStructureSheafHom f)

/-- The restriction of an `\mathcal O_X`-module to an open subspace. -/
abbrev restrictedRingedSpaceModule {X : RingedSpace.{u}}
    (U : Opens X.carrier) (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) :=
  (moduleSheafRestrictionToOpen U (ringedSpaceRingCatSheaf X)).obj ℱ

/-- Pushforward of modules from an open subspace back to the ambient ringed space. -/
noncomputable abbrev ringedSpaceModulePushforwardFromOpen
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj
        (ringedSpaceRingCatSheaf X)) ⥤
      SheafOfModules (ringedSpaceRingCatSheaf X) :=
  SheafOfModules.pushforward
    (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
      (ringedSpaceRingCatSheaf X)))

/-- The composite direct image `a_*` obtained by first pushing forward from an open subspace to
`X` and then along `f : X ⟶ Y`. -/
abbrev ringedSpaceModulePushforwardAlongOpen
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (U : Opens X.carrier) :=
  ringedSpaceModulePushforwardFromOpen U ⋙ ringedSpaceModulePushforward f

/-- The biproduct of the two open-subspace direct images appearing in relative Mayer-Vietoris. -/
abbrev relativeMayerVietorisMiddleTerm
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (U V : Opens X.carrier)
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) :=
  ((ringedSpaceModulePushforwardAlongOpen f U).obj (restrictedRingedSpaceModule U ℱ)) ⊞
    ((ringedSpaceModulePushforwardAlongOpen f V).obj (restrictedRingedSpaceModule V ℱ))

/-- The direct-image term coming from the intersection `U ∩ V` in relative Mayer-Vietoris. -/
abbrev relativeMayerVietorisIntersectionTerm
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (U V : Opens X.carrier)
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) :=
  (ringedSpaceModulePushforwardAlongOpen f (U ⊓ V)).obj
    (restrictedRingedSpaceModule (U ⊓ V) ℱ)

/-- The map on the left term induced by a morphism of `\mathcal O_X`-modules. -/
abbrev relativeMayerVietorisLeftMap
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    {ℱ 𝒢 : SheafOfModules (ringedSpaceRingCatSheaf X)} (φ : ℱ ⟶ 𝒢) :=
  (ringedSpaceModulePushforward f).map φ

/-- The map on the middle biproduct term induced by a morphism of `\mathcal O_X`-modules. -/
abbrev relativeMayerVietorisMiddleMap
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (U V : Opens X.carrier)
    {ℱ 𝒢 : SheafOfModules (ringedSpaceRingCatSheaf X)} (φ : ℱ ⟶ 𝒢) :=
  biprod.map
    ((ringedSpaceModulePushforwardAlongOpen f U).map
      ((moduleSheafRestrictionToOpen U (ringedSpaceRingCatSheaf X)).map φ))
    ((ringedSpaceModulePushforwardAlongOpen f V).map
      ((moduleSheafRestrictionToOpen V (ringedSpaceRingCatSheaf X)).map φ))

/-- The map on the intersection term induced by a morphism of `\mathcal O_X`-modules. -/
abbrev relativeMayerVietorisIntersectionMap
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (U V : Opens X.carrier)
    {ℱ 𝒢 : SheafOfModules (ringedSpaceRingCatSheaf X)} (φ : ℱ ⟶ 𝒢) :=
  (ringedSpaceModulePushforwardAlongOpen f (U ⊓ V)).map
    ((moduleSheafRestrictionToOpen (U ⊓ V) (ringedSpaceRingCatSheaf X)).map φ)

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [(ringedSpaceModulePushforward f).Additive]
variable [HasInjectiveResolutions (SheafOfModules (ringedSpaceRingCatSheaf X))]

-- Proof sketch: start from the standard short exact sequence
-- `0 ⟶ ℱ ⟶ j_{U,*}(ℱ|_U) ⊞ j_{V,*}(ℱ|_V) ⟶ j_{U∩V,*}(ℱ|_{U∩V}) ⟶ 0`
-- on `X`, apply the left exact functor `f_*`, and take the first connecting morphism in the
-- associated long exact sequence of right derived functors.
/-- Lemma 20.8.3 (Relative Mayer-Vietoris): if `f : X ⟶ Y` is a morphism of ringed spaces and
`X = U ∪ V`, then for every `\mathcal O_X`-module `\mathcal F` there is an initial exact segment
`0 ⟶ f_* \mathcal F ⟶ a_*(\mathcal F|_U) ⊞ b_*(\mathcal F|_V) ⟶
c_*(\mathcal F|_{U \cap V}) ⟶ R^1 f_* \mathcal F`
of the relative Mayer-Vietoris long exact sequence. -/
theorem ringedSpaceModule_relativeMayerVietoris
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) :
    ∃ α : (ringedSpaceModulePushforward f).obj ℱ ⟶ relativeMayerVietorisMiddleTerm f U V ℱ,
      ∃ β : relativeMayerVietorisMiddleTerm f U V ℱ ⟶
          relativeMayerVietorisIntersectionTerm f U V ℱ,
        ∃ δ : relativeMayerVietorisIntersectionTerm f U V ℱ ⟶
            ((ringedSpaceModulePushforward f).rightDerived 1).obj ℱ,
          Mono α ∧ (ComposableArrows.mk₃ α β δ).Exact := sorry

-- Proof sketch: choose relative Mayer-Vietoris segments for `ℱ` and `𝒢` from the previous
-- theorem, then use the naturality of restriction, of the biproduct maps, and of the connecting
-- morphism in the right-derived long exact sequence to obtain commuting squares.
/-- A morphism of `\mathcal O_X`-modules induces a compatible morphism between suitable choices of
the initial relative Mayer-Vietoris segments. -/
theorem ringedSpaceModule_relativeMayerVietoris_functorial
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    {ℱ 𝒢 : SheafOfModules (ringedSpaceRingCatSheaf X)} (φ : ℱ ⟶ 𝒢) :
    ∃ αℱ : (ringedSpaceModulePushforward f).obj ℱ ⟶ relativeMayerVietorisMiddleTerm f U V ℱ,
      ∃ βℱ : relativeMayerVietorisMiddleTerm f U V ℱ ⟶
          relativeMayerVietorisIntersectionTerm f U V ℱ,
        ∃ δℱ : relativeMayerVietorisIntersectionTerm f U V ℱ ⟶
            ((ringedSpaceModulePushforward f).rightDerived 1).obj ℱ,
          ∃ α𝒢 : (ringedSpaceModulePushforward f).obj 𝒢 ⟶ relativeMayerVietorisMiddleTerm f U V 𝒢,
            ∃ β𝒢 : relativeMayerVietorisMiddleTerm f U V 𝒢 ⟶
                relativeMayerVietorisIntersectionTerm f U V 𝒢,
              ∃ δ𝒢 : relativeMayerVietorisIntersectionTerm f U V 𝒢 ⟶
                  ((ringedSpaceModulePushforward f).rightDerived 1).obj 𝒢,
                Mono αℱ ∧ (ComposableArrows.mk₃ αℱ βℱ δℱ).Exact ∧
                  Mono α𝒢 ∧ (ComposableArrows.mk₃ α𝒢 β𝒢 δ𝒢).Exact ∧
                  relativeMayerVietorisLeftMap f φ ≫ α𝒢 =
                    αℱ ≫ relativeMayerVietorisMiddleMap f U V φ ∧
                  relativeMayerVietorisMiddleMap f U V φ ≫ β𝒢 =
                    βℱ ≫ relativeMayerVietorisIntersectionMap f U V φ ∧
                  relativeMayerVietorisIntersectionMap f U V φ ≫ δ𝒢 =
                    δℱ ≫ ((ringedSpaceModulePushforward f).rightDerived 1).map φ := sorry

end AlgebraicGeometry
