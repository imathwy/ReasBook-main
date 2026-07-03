import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import StacksProject_2024.Chap21.Definition_21_44_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The unbounded derived category `D(\mathcal O)` of module sheaves on a ringed site. -/
abbrev RingedSiteDerived (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u}) :=
  DerivedCategory (RingedSiteModules J 𝒪)

/-- The quasi-isomorphisms in the homotopy category of cochain complexes of `\mathcal O`-modules.
-/
abbrev RingedSiteQis (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u}) :=
  HomotopyCategory.quasiIso (RingedSiteModules J 𝒪) (up ℤ)

variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪' : Sheaf JC CommRingCat.{u}} {𝒪 : Sheaf JD CommRingCat.{u}}
variable (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪)

/-- The underlying `RingCat`-valued structure map attached to the site-presented morphism of
ringed topoi determined by `φ`. -/
abbrev ringedSiteUnderlyingStructureMap
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪) :
    (sheafCompose JC (forget₂ CommRingCat RingCat)).obj 𝒪' ⟶
      (F.sheafPushforwardContinuous RingCat.{u} JC JD).obj
        ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪) :=
  (sheafCompose JC (forget₂ CommRingCat RingCat)).map φ

variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]

/-- The inverse-image functor on module sheaves attached to the site-presented morphism of ringed
topoi determined by `φ`. -/
abbrev pullbackFunctor
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪) :
    RingedSiteModules JC 𝒪' ⥤ RingedSiteModules JD 𝒪 :=
  SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)

variable [Abelian (RingedSiteModules JC 𝒪')]
variable [CategoryWithHomology (RingedSiteModules JC 𝒪')]
variable [Abelian (RingedSiteModules JD 𝒪)]
variable [CategoryWithHomology (RingedSiteModules JD 𝒪)]
variable [MonoidalCategory (RingedSiteModules JC 𝒪')]
variable [MonoidalPreadditive (RingedSiteModules JC 𝒪')]
variable [MonoidalCategory (RingedSiteModules JD 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules JD 𝒪)]
variable [(pullbackFunctor F φ).Additive]

local instance instPreadditiveTarget : Preadditive (RingedSiteModules JC 𝒪') :=
  (inferInstance : Abelian (RingedSiteModules JC 𝒪')).toPreadditive

local instance instPreadditiveSource : Preadditive (RingedSiteModules JD 𝒪) :=
  (inferInstance : Abelian (RingedSiteModules JD 𝒪)).toPreadditive

/-- The quasi-isomorphisms in the homotopy category of complexes of `\mathcal O'`-modules,
recorded using the local `Preadditive` instance induced from the abelian structure. -/
private abbrev sourceQis :
    MorphismProperty (HomotopyCategory (RingedSiteModules JC 𝒪') (up ℤ)) :=
  HomotopyCategory.quasiIso (RingedSiteModules JC 𝒪') (up ℤ)

/-- The functor on homotopy categories induced by pullback of module sheaves for the
site-presented morphism of ringed topoi determined by `φ`. -/
abbrev pullbackToDerived :
    HomotopyCategory (RingedSiteModules JC 𝒪') (up ℤ) ⥤
      DerivedCategory (RingedSiteModules JD 𝒪) :=
  (pullbackFunctor F φ).mapHomotopyCategory (up ℤ) ⋙
    (show HomotopyCategory (RingedSiteModules JD 𝒪) (up ℤ) ⥤
        DerivedCategory (RingedSiteModules JD 𝒪) from
      (DerivedCategory.Qh :
        HomotopyCategory (RingedSiteModules JD 𝒪) (up ℤ) ⥤
          DerivedCategory (RingedSiteModules JD 𝒪)))

-- Proof sketch: apply the total-left-derived-functor existence criterion to the homotopy-level
-- pullback functor. The intended proof later uses K-flat resolutions with flat terms to show that
-- pullback sends quasi-isomorphisms between suitable resolutions to quasi-isomorphisms.
/-- The homotopy-level pullback functor attached to the site-presented morphism of ringed topoi
determined by `φ` has an everywhere-defined total left derived functor. -/
theorem pullbackToDerived_hasLeftDerivedFunctor :
    Functor.HasLeftDerivedFunctor
      (pullbackToDerived F φ)
      sourceQis := sorry

/-- The homotopy-level pullback functor for the site-presented morphism of ringed topoi determined
by `φ` has its canonical total left derived functor. -/
instance pullbackFunctor_hasLeftDerivedFunctor :
    Functor.HasLeftDerivedFunctor
      (pullbackToDerived F φ)
      sourceQis :=
  pullbackToDerived_hasLeftDerivedFunctor F φ

/-- The derived pullback functor `Lf^* : D(\mathcal O') \to D(\mathcal O)` attached to the
site-presented morphism of ringed topoi determined by `φ`. -/
noncomputable abbrev leftDerivedPullback :
    DerivedCategory (RingedSiteModules JC 𝒪') ⥤
      DerivedCategory (RingedSiteModules JD 𝒪) :=
  Functor.totalLeftDerived
    (pullbackToDerived F φ)
    (show HomotopyCategory (RingedSiteModules JC 𝒪') (up ℤ) ⥤
        DerivedCategory (RingedSiteModules JC 𝒪') from
      (DerivedCategory.Qh :
        HomotopyCategory (RingedSiteModules JC 𝒪') (up ℤ) ⥤
          DerivedCategory (RingedSiteModules JC 𝒪')))
    sourceQis

/-- The derived pullback functor `Lf^*` specialized to the fixed site-presented morphism of ringed
topoi determined by `φ`. -/
noncomputable abbrev leftDerivedPullbackFunctor :=
  leftDerivedPullback F φ

local notation "Lf" => leftDerivedPullbackFunctor F φ

variable
  (derivedTensorTarget :
    DerivedCategory (RingedSiteModules JC 𝒪') ⥤
      DerivedCategory (RingedSiteModules JC 𝒪') ⥤
        DerivedCategory (RingedSiteModules JC 𝒪'))
  (derivedTensorSource :
    DerivedCategory (RingedSiteModules JD 𝒪) ⥤
      DerivedCategory (RingedSiteModules JD 𝒪) ⥤
        DerivedCategory (RingedSiteModules JD 𝒪))

-- Proof sketch: replace both inputs by K-flat complexes with flat terms, compute both derived
-- tensor products by total tensor complexes, and compare the resulting ordinary pullback-tensor
-- constructions using the underived tensor compatibility from Lemma `18.26.2`. The
-- quasi-isomorphism-invariance of derived pullback and derived tensor product then descends this
-- comparison to the derived categories, and functoriality in both variables comes from the
-- naturality of the termwise comparison morphisms.
/-- Lemma 21.18.4: for the site-presented morphism of ringed topoi determined by `φ`, there is a
canonical bifunctorial isomorphism identifying the derived pullback of the derived tensor product
over `\mathcal O'` with the derived tensor product over `\mathcal O` of the two derived
pullbacks. -/
theorem leftDerivedPullback_tensorComparison :
    ∃ η :
      ∀ (ℱ 𝒢 : DerivedCategory (RingedSiteModules JC 𝒪')),
        ((Lf).obj (((derivedTensorTarget).obj 𝒢).obj ℱ)) ≅
          (((derivedTensorSource).obj ((Lf).obj 𝒢)).obj
            ((Lf).obj ℱ)),
      ∀ {ℱ₁ ℱ₂ : DerivedCategory (RingedSiteModules JC 𝒪')}
          {𝒢₁ 𝒢₂ : DerivedCategory (RingedSiteModules JC 𝒪')}
          (fℱ : ℱ₁ ⟶ ℱ₂) (f𝒢 : 𝒢₁ ⟶ 𝒢₂),
        (Lf).map
            ((((derivedTensorTarget).map f𝒢).app ℱ₁) ≫
              (((derivedTensorTarget).obj 𝒢₂).map fℱ)) ≫
          (η ℱ₂ 𝒢₂).hom =
        (η ℱ₁ 𝒢₁).hom ≫
          (((derivedTensorSource).map ((Lf).map f𝒢)).app ((Lf).obj ℱ₁)) ≫
          (((derivedTensorSource).obj ((Lf).obj 𝒢₂)).map ((Lf).map fℱ)) := sorry

end

end SheafOfModules.RingedSite
