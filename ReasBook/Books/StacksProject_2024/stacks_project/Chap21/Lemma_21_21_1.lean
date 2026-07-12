import StacksProject_2024.Chap07.Lemma_7_27_5
import StacksProject_2024.Chap13.Lemma_13_30_1
import StacksProject_2024.Chap19.AdditiveFunctorTotalRightDerived
import StacksProject_2024.Chap21.SiteAbelianDerived
import StacksProject_2024.Chap21.Remark_21_19_3_core
import Mathlib.CategoryTheory.Adjunction.Mates

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor

namespace CategoryTheory

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [∀ X : C, IsGrothendieckAbelian.{u} (SiteAbelianSheafCat (J.over X))]

/- Domain-style sampling for Lemma 21.21.1:
- primary domain: derived base change for abelian sheaves on slice sites of a Grothendieck
  topology;
- sampled owner declarations:
  `Functor.mapDerivedCategory`,
  `CategoryTheory.derivedBaseChangeMap`,
  `CategoryTheory.additiveFunctorTotalRightDerived`,
  `CategoryTheory.IsDerivedBaseChangeMap`;
- owner abstraction:
  `source-facing`: the functor-level relocalization base-change comparison on the derived category
    of abelian sheaves over slice sites;
  `core/canonical`: `CategoryTheory.derivedBaseChangeMap`, with left side given by the exact
    slice-site inverse-image owner `(J.overMapPullback AddCommGrpCat f).mapDerivedCategory` and
    right side given by the canonical derived direct-image owner
    `additiveFunctorTotalRightDerived
      ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat (J.over X) (J.over Y))`;
  `bridge/view`: the derived relocalization square comparison is explicit bridge data, together
    with the derived pullback-pushforward adjunctions `adj_f`, `adj_p` on the slice sites.
-/

variable {X' X Y' Y : C}
variable (i : X' ⟶ X) (p : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
variable [Functor.Additive (J.overMapPullback AddCommGrpCat.{u} f)]
variable [PreservesFiniteLimits (J.overMapPullback AddCommGrpCat.{u} f)]
variable [PreservesFiniteColimits (J.overMapPullback AddCommGrpCat.{u} f)]
variable [Functor.Additive (J.overMapPullback AddCommGrpCat.{u} p)]
variable [PreservesFiniteLimits (J.overMapPullback AddCommGrpCat.{u} p)]
variable [PreservesFiniteColimits (J.overMapPullback AddCommGrpCat.{u} p)]
variable [Functor.Additive (J.overMapPullback AddCommGrpCat.{u} g)]
variable [PreservesFiniteLimits (J.overMapPullback AddCommGrpCat.{u} g)]
variable [PreservesFiniteColimits (J.overMapPullback AddCommGrpCat.{u} g)]
variable [Functor.Additive (J.overMapPullback AddCommGrpCat.{u} i)]
variable [PreservesFiniteLimits (J.overMapPullback AddCommGrpCat.{u} i)]
variable [PreservesFiniteColimits (J.overMapPullback AddCommGrpCat.{u} i)]
variable [∀ F : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u}, (Over.map f).op.HasPointwiseRightKanExtension F]
variable [∀ F : (Over X')ᵒᵖ ⥤ AddCommGrpCat.{u}, (Over.map p).op.HasPointwiseRightKanExtension F]
variable [Functor.Additive
  ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u} (J.over X) (J.over Y))]
variable [Functor.Additive
  ((Over.map p).sheafPushforwardCocontinuous AddCommGrpCat.{u} (J.over X') (J.over Y'))]

local notation "DAb[" X "]" => DerivedCategory (SiteAbelianSheafCat (J.over X))

private noncomputable def mapDerivedCategoryIsoOfNatIso
    {A : Type*} {B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (F G : A ⥤ B)
    [Functor.Additive F] [Functor.Additive G]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory := by
  let QA : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  let QB : CochainComplex B ℤ ⥤ DerivedCategory B := DerivedCategory.Q
  exact
    Localization.liftNatIso
      QA
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QB)
      (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QB)
      F.mapDerivedCategory
      G.mapDerivedCategory
      (Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ))
        QB)

private noncomputable def mapDerivedCategoryCompIso
    {A : Type*} {B : Type*} {D : Type*}
    [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    (F : A ⥤ B) (G : B ⥤ D)
    [Functor.Additive F] [Functor.Additive G]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ (F ⋙ G).mapDerivedCategory := by
  let QA : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  let QB : CochainComplex B ℤ ⥤ DerivedCategory B := DerivedCategory.Q
  let QD : CochainComplex D ℤ ⥤ DerivedCategory D := DerivedCategory.Q
  let eFactors :
      ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QB) ⋙ G.mapDerivedCategory) ≅
        (F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QD := by
    simpa using
      (Functor.associator
        (F.mapHomologicalComplex (ComplexShape.up ℤ))
        QB
        G.mapDerivedCategory) ≪≫
      Functor.isoWhiskerLeft
        (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (show QB ⋙ G.mapDerivedCategory ≅
            G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QD from
          G.mapDerivedCategoryFactors)
  letI :
      Localization.Lifting
        QA
        (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
        ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QB) ⋙ G.mapDerivedCategory)
        (F.mapDerivedCategory ⋙ G.mapDerivedCategory) :=
    Localization.Lifting.compRight
      QA
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QB)
      F.mapDerivedCategory
      G.mapDerivedCategory
  exact
    Localization.liftNatIso
      QA
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QB) ⋙ G.mapDerivedCategory)
      ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QD)
      (F.mapDerivedCategory ⋙ G.mapDerivedCategory)
      ((F ⋙ G).mapDerivedCategory)
      eFactors

private noncomputable def relocalizationDerivedSquareIso
    (hcart : IsPullback i p f g) :
    (J.overMapPullback AddCommGrpCat.{u} g).mapDerivedCategory ⋙
        (J.overMapPullback AddCommGrpCat.{u} p).mapDerivedCategory ≅
      (J.overMapPullback AddCommGrpCat.{u} f).mapDerivedCategory ⋙
        (J.overMapPullback AddCommGrpCat.{u} i).mapDerivedCategory :=
  let gpComp :
      (J.overMapPullback AddCommGrpCat.{u} g).mapDerivedCategory ⋙
          (J.overMapPullback AddCommGrpCat.{u} p).mapDerivedCategory ≅
        ((J.overMapPullback AddCommGrpCat.{u} g) ⋙
          (J.overMapPullback AddCommGrpCat.{u} p)).mapDerivedCategory :=
    mapDerivedCategoryCompIso
      (J.overMapPullback AddCommGrpCat.{u} g)
      (J.overMapPullback AddCommGrpCat.{u} p)
  let squareComp :
      ((J.overMapPullback AddCommGrpCat.{u} g) ⋙
          (J.overMapPullback AddCommGrpCat.{u} p)).mapDerivedCategory ≅
        ((J.overMapPullback AddCommGrpCat.{u} f) ⋙
          (J.overMapPullback AddCommGrpCat.{u} i)).mapDerivedCategory :=
    mapDerivedCategoryIsoOfNatIso
      ((J.overMapPullback AddCommGrpCat.{u} g) ⋙
        (J.overMapPullback AddCommGrpCat.{u} p))
      ((J.overMapPullback AddCommGrpCat.{u} f) ⋙
        (J.overMapPullback AddCommGrpCat.{u} i))
      (relocalization_inverse_image_square_iso J i p f g hcart.w).symm
  let fiComp :
      (J.overMapPullback AddCommGrpCat.{u} f).mapDerivedCategory ⋙
          (J.overMapPullback AddCommGrpCat.{u} i).mapDerivedCategory ≅
        ((J.overMapPullback AddCommGrpCat.{u} f) ⋙
          (J.overMapPullback AddCommGrpCat.{u} i)).mapDerivedCategory :=
    mapDerivedCategoryCompIso
      (J.overMapPullback AddCommGrpCat.{u} f)
      (J.overMapPullback AddCommGrpCat.{u} i)
  gpComp ≪≫ squareComp ≪≫ fiComp.symm

/-- Helper for Lemma 21.21.1: `DerivedCategory.Qh` sends homotopy quasi-isomorphisms on slice-site
abelian sheaf complexes to isomorphisms. -/
private theorem qh_map_isIso_of_homotopyQuasiIso
    {A : C}
    {K L : HomotopyCategory (SiteAbelianSheafCat (J.over A)) (ComplexShape.up ℤ)}
    (u : K ⟶ L)
    (hu : (HomotopyCategory.quasiIso
      (SiteAbelianSheafCat (J.over A))
      (ComplexShape.up ℤ)) u) :
    IsIso (DerivedCategory.Qh.map u) := by
  -- Proof comment: the derived category is the localization of the homotopy category at
  -- quasi-isomorphisms, so `Qh` carries every denominator to an isomorphism.
  exact (DerivedCategory.isIso_Qh_map_iff u).2 hu

/-- Helper for Lemma 21.21.1: the comparison `quotient ⋙ Qh ≅ Q` is objectwise an isomorphism on
slice-site abelian sheaf complexes. -/
private theorem quotientCompQhIso_hom_app_isIso
    {A : C}
    (K : CochainComplex (SiteAbelianSheafCat (J.over A)) ℤ) :
    IsIso ((DerivedCategory.quotientCompQhIso (SiteAbelianSheafCat (J.over A))).hom.app K) := by
  -- Proof comment: this is just the componentwise isomorphism of the canonical comparison
  -- `quotient ⋙ Qh ≅ Q`.
  exact (NatTrans.isIso_iff_isIso_app _).1 inferInstance K

/-- Helper for Lemma 21.21.1: conjugating a `Qh`-image along `quotientCompQhIso` recovers the
corresponding `DerivedCategory.Q` map on slice-site abelian sheaf complexes. -/
private theorem quotientCompQhIso_homCongr_map
    {A : C}
    {K L : CochainComplex (SiteAbelianSheafCat (J.over A)) ℤ}
    (u : K ⟶ L) :
    (Iso.homCongr
        ((DerivedCategory.quotientCompQhIso (SiteAbelianSheafCat (J.over A))).app K)
        ((DerivedCategory.quotientCompQhIso (SiteAbelianSheafCat (J.over A))).app L))
      (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (SiteAbelianSheafCat (J.over A)) (ComplexShape.up ℤ)).map u)) =
      DerivedCategory.Q.map u := by
  -- Proof comment: this is the naturality square of `quotientCompQhIso`, rewritten after
  -- conjugating the `Qh`-morphism back to the `Q`-surface.
  change
    (DerivedCategory.quotientCompQhIso (SiteAbelianSheafCat (J.over A))).inv.app K ≫
        DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (SiteAbelianSheafCat (J.over A)) (ComplexShape.up ℤ)).map u) ≫
          (DerivedCategory.quotientCompQhIso (SiteAbelianSheafCat (J.over A))).hom.app L =
      DerivedCategory.Q.map u
  have hnat :
      DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (SiteAbelianSheafCat (J.over A)) (ComplexShape.up ℤ)).map u) ≫
          (DerivedCategory.quotientCompQhIso (SiteAbelianSheafCat (J.over A))).hom.app L =
        (DerivedCategory.quotientCompQhIso (SiteAbelianSheafCat (J.over A))).hom.app K ≫
          DerivedCategory.Q.map u := by
    simpa [Functor.comp_map] using
      ((DerivedCategory.quotientCompQhIso (SiteAbelianSheafCat (J.over A))).hom.naturality u).symm
  calc
    (DerivedCategory.quotientCompQhIso (SiteAbelianSheafCat (J.over A))).inv.app K ≫
        DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (SiteAbelianSheafCat (J.over A)) (ComplexShape.up ℤ)).map u) ≫
          (DerivedCategory.quotientCompQhIso (SiteAbelianSheafCat (J.over A))).hom.app L =
      (DerivedCategory.quotientCompQhIso (SiteAbelianSheafCat (J.over A))).inv.app K ≫
        ((DerivedCategory.quotientCompQhIso (SiteAbelianSheafCat (J.over A))).hom.app K ≫
          DerivedCategory.Q.map u) := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦
                  (DerivedCategory.quotientCompQhIso
                    (SiteAbelianSheafCat (J.over A))).inv.app K ≫ k)
                hnat
    _ = DerivedCategory.Q.map u := by
      simpa [Category.assoc] using
        Iso.inv_hom_id_assoc
          ((DerivedCategory.quotientCompQhIso (SiteAbelianSheafCat (J.over A))).app K)
          (DerivedCategory.Q.map u)

/-- Helper for Lemma 21.21.1: the homotopy-side slice-site pushforward functor has a pointwise
right derived functor because every complex admits a quasi-isomorphic K-injective replacement. -/
private theorem pushforwardHomotopy_hasPointwiseRightDerivedFunctor
    {A B : C} (q : A ⟶ B)
    [Functor.Additive
      ((Over.map q).sheafPushforwardCocontinuous
        AddCommGrpCat.{u} (J.over A) (J.over B))] :
    Functor.HasPointwiseRightDerivedFunctor
      (((Over.map q).sheafPushforwardCocontinuous
          AddCommGrpCat.{u} (J.over A) (J.over B)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh)
      (HomotopyCategory.quasiIso
        (SiteAbelianSheafCat (J.over A))
        (ComplexShape.up ℤ)) := by
  let F :
      HomotopyCategory (SiteAbelianSheafCat (J.over A)) (ComplexShape.up ℤ) ⥤
        DerivedCategory (SiteAbelianSheafCat (J.over B)) :=
    ((Over.map q).sheafPushforwardCocontinuous
      AddCommGrpCat.{u} (J.over A) (J.over B)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh
  let Qish :
      MorphismProperty
        (HomotopyCategory (SiteAbelianSheafCat (J.over A)) (ComplexShape.up ℤ)) :=
    HomotopyCategory.quasiIso
      (SiteAbelianSheafCat (J.over A))
      (ComplexShape.up ℤ)
  -- Proof comment: replicate the Chapter 13 K-injective-resolution existence argument on the
  -- homotopy side, so every object is connected to a computing K-injective representative.
  refine F.hasPointwiseRightDerivedFunctor_of_exists_computesRightDerivedAt Qish ?_
  intro K
  obtain ⟨Kinj, _, hKinj⟩ :=
    CochainComplex.exists_functorial_kInjective_resolution
      (SiteAbelianSheafCat (J.over A))
  refine
    ⟨(HomotopyCategory.quotient
        (SiteAbelianSheafCat (J.over A))
        (ComplexShape.up ℤ)).obj
        (Kinj.toFunctor.obj K.as), ?_, ?_, ?_⟩
  · -- The chosen functorial replacement arrow gives the required comparison in the homotopy
    -- category after rewriting `K` back to its quotient model.
    simpa [HomotopyCategory.quotient_obj_as] using
      (HomotopyCategory.quotient
        (SiteAbelianSheafCat (J.over A))
        (ComplexShape.up ℤ)).map
        (Kinj.ι.app K.as)
  · -- The replacement arrow is a quasi-isomorphism by construction.
    exact
      (HomotopyCategory.quotient_map_mem_quasiIso_iff
        (Kinj.ι.app K.as)).2
        (Kinj.quasiIso_app K.as)
  · -- A K-injective target computes the right derived functor at that object.
    letI : (Kinj.toFunctor.obj K.as).IsKInjective := hKinj K.as
    simpa [F, Qish] using
      (kInjective_computesRightDerivedFunctorAt
        F
        (Kinj.toFunctor.obj K.as))

/-- Helper for Lemma 21.21.1: on a K-injective complex, the homotopy-side total right derived
unit for slice-site pushforward is an isomorphism. -/
private theorem pushforwardHomotopy_computesRightDerivedAt_of_isKInjective
    {A B : C} (q : A ⟶ B)
    [Functor.Additive
      ((Over.map q).sheafPushforwardCocontinuous
        AddCommGrpCat.{u} (J.over A) (J.over B))]
    (I : CochainComplex (SiteAbelianSheafCat (J.over A)) ℤ) [I.IsKInjective] :
    let F :
        HomotopyCategory (SiteAbelianSheafCat (J.over A)) (ComplexShape.up ℤ) ⥤
          DerivedCategory (SiteAbelianSheafCat (J.over B)) :=
      ((Over.map q).sheafPushforwardCocontinuous
        AddCommGrpCat.{u} (J.over A) (J.over B)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh
    let Qish :
        MorphismProperty
          (HomotopyCategory (SiteAbelianSheafCat (J.over A)) (ComplexShape.up ℤ)) :=
      HomotopyCategory.quasiIso
        (SiteAbelianSheafCat (J.over A))
        (ComplexShape.up ℤ)
    F.ComputesRightDerivedAt
      Qish
      ((HomotopyCategory.quotient (SiteAbelianSheafCat (J.over A)) (ComplexShape.up ℤ)).obj I) := by
  let F :
      HomotopyCategory (SiteAbelianSheafCat (J.over A)) (ComplexShape.up ℤ) ⥤
        DerivedCategory (SiteAbelianSheafCat (J.over B)) :=
    ((Over.map q).sheafPushforwardCocontinuous
      AddCommGrpCat.{u} (J.over A) (J.over B)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh
  let Qish :
      MorphismProperty
        (HomotopyCategory (SiteAbelianSheafCat (J.over A)) (ComplexShape.up ℤ)) :=
    HomotopyCategory.quasiIso
      (SiteAbelianSheafCat (J.over A))
      (ComplexShape.up ℤ)
  -- Proof comment: K-injective representatives compute the homotopy-side derived pushforward at
  -- the quotient object, exactly as in the source proof.
  simpa [F, Qish] using
    (kInjective_computesRightDerivedFunctorAt
      F
      I)

/-- Helper for Lemma 21.21.1: on a K-injective complex, the homotopy-side total right derived
unit for slice-site pushforward is an isomorphism. -/
private theorem pushforwardHomotopyUnit_app_isIso_of_isKInjective
    {A B : C} (q : A ⟶ B)
    [Functor.Additive
      ((Over.map q).sheafPushforwardCocontinuous
        AddCommGrpCat.{u} (J.over A) (J.over B))]
    (I : CochainComplex (SiteAbelianSheafCat (J.over A)) ℤ) [I.IsKInjective] :
    IsIso
      ((Functor.totalRightDerivedUnit
          (((Over.map q).sheafPushforwardCocontinuous
              AddCommGrpCat.{u} (J.over A) (J.over B)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh)
          DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (SiteAbelianSheafCat (J.over A))
            (ComplexShape.up ℤ))).app
        ((HomotopyCategory.quotient (SiteAbelianSheafCat (J.over A)) (ComplexShape.up ℤ)).obj I)) := by
  let F :
      HomotopyCategory (SiteAbelianSheafCat (J.over A)) (ComplexShape.up ℤ) ⥤
        DerivedCategory (SiteAbelianSheafCat (J.over B)) :=
    ((Over.map q).sheafPushforwardCocontinuous
      AddCommGrpCat.{u} (J.over A) (J.over B)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh
  let Qish :
      MorphismProperty
        (HomotopyCategory (SiteAbelianSheafCat (J.over A)) (ComplexShape.up ℤ)) :=
    HomotopyCategory.quasiIso
      (SiteAbelianSheafCat (J.over A))
      (ComplexShape.up ℤ)
  let _ : Functor.HasPointwiseRightDerivedFunctor F Qish :=
    pushforwardHomotopy_hasPointwiseRightDerivedFunctor J q
  have hcomp :
      F.ComputesRightDerivedAt
        Qish
        ((HomotopyCategory.quotient
          (SiteAbelianSheafCat (J.over A))
          (ComplexShape.up ℤ)).obj I) :=
    pushforwardHomotopy_computesRightDerivedAt_of_isKInjective J q I
  -- TODO: re-establish the bridge from `ComputesRightDerivedAt` on the homotopy-side owner `F`
  -- to invertibility of its canonical total-right-derived unit component at the quotient object.
  -- The current proof term no longer elaborates after the owner changed from the abstract
  -- localization functor `Qish.Q` to the concrete `DerivedCategory.Qh`.
  sorry

/-- Helper for Lemma 21.21.1: a K-injective complex computes the chosen total right derived
pushforward, so the cochain-level comparison map to `additiveFunctorTotalRightDerived` is an
isomorphism. -/
private theorem pushforwardDerivedUnit_app_isIso_of_isKInjective
    {A B : C} (q : A ⟶ B)
    [Functor.Additive
      ((Over.map q).sheafPushforwardCocontinuous
        AddCommGrpCat.{u} (J.over A) (J.over B))]
    (I : CochainComplex (SiteAbelianSheafCat (J.over A)) ℤ) [I.IsKInjective] :
    IsIso
      ((additiveFunctorTotalRightDerivedUnit
        ((Over.map q).sheafPushforwardCocontinuous
          AddCommGrpCat.{u} (J.over A) (J.over B))).app I) := by
  let F : SiteAbelianSheafCat (J.over A) ⥤ SiteAbelianSheafCat (J.over B) :=
    (Over.map q).sheafPushforwardCocontinuous
      AddCommGrpCat.{u} (J.over A) (J.over B)
  let QhA :
      HomotopyCategory (SiteAbelianSheafCat (J.over A)) (ComplexShape.up ℤ) ⥤
        DerivedCategory (SiteAbelianSheafCat (J.over A)) :=
    DerivedCategory.Qh
  let QhB :
      HomotopyCategory (SiteAbelianSheafCat (J.over B)) (ComplexShape.up ℤ) ⥤
        DerivedCategory (SiteAbelianSheafCat (J.over B)) :=
    DerivedCategory.Qh
  let QA :
      CochainComplex (SiteAbelianSheafCat (J.over A)) ℤ ⥤
        DerivedCategory (SiteAbelianSheafCat (J.over A)) :=
    DerivedCategory.Q
  let QB :
      CochainComplex (SiteAbelianSheafCat (J.over B)) ℤ ⥤
        DerivedCategory (SiteAbelianSheafCat (J.over B)) :=
    DerivedCategory.Q
  let η :
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ QhB ⟶
        QhA ⋙ additiveFunctorTotalRightDerived F :=
    Functor.totalRightDerivedUnit
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ QhB)
      QhA
      (HomotopyCategory.quasiIso
        (SiteAbelianSheafCat (J.over A))
        (ComplexShape.up ℤ))
  let eSource :
      HomotopyCategory.quotient
          (SiteAbelianSheafCat (J.over A))
          (ComplexShape.up ℤ) ⋙
        (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ QhB) ≅
          F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QB :=
    (Functor.associator
      (HomotopyCategory.quotient
        (SiteAbelianSheafCat (J.over A))
        (ComplexShape.up ℤ))
      (F.mapHomotopyCategory (ComplexShape.up ℤ))
      QhB).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryFactors F (ComplexShape.up ℤ))
        QhB ≪≫
      Functor.associator
        (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (HomotopyCategory.quotient
          (SiteAbelianSheafCat (J.over B))
          (ComplexShape.up ℤ))
        QhB ≪≫
      Functor.isoWhiskerLeft
        (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.quotientCompQhIso (SiteAbelianSheafCat (J.over B)))
  have hη :
      IsIso
        ((Functor.whiskerLeft
          (HomotopyCategory.quotient
            (SiteAbelianSheafCat (J.over A))
            (ComplexShape.up ℤ))
          η).app I) := by
    -- Proof comment: after whiskering with the quotient functor, this is exactly the
    -- homotopy-side K-injective unit component proved above.
    simpa [η, F, QhA, QhB] using
      (pushforwardHomotopyUnit_app_isIso_of_isKInjective
        J q I)
  letI :
      IsIso
        ((Functor.whiskerLeft
          (HomotopyCategory.quotient
            (SiteAbelianSheafCat (J.over A))
            (ComplexShape.up ℤ))
          η).app I) :=
    hη
  let e :
      ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QB).obj I) ≅
        ((QA ⋙ additiveFunctorTotalRightDerived F).obj I) :=
    (eSource.app I).symm ≪≫
      asIso
        ((Functor.whiskerLeft
          (HomotopyCategory.quotient
            (SiteAbelianSheafCat (J.over A))
            (ComplexShape.up ℤ))
          η).app I) ≪≫
      (Functor.associator
        (HomotopyCategory.quotient
          (SiteAbelianSheafCat (J.over A))
          (ComplexShape.up ℤ))
        QhA
        (additiveFunctorTotalRightDerived F)).app I ≪≫
      (Functor.isoWhiskerRight
        (DerivedCategory.quotientCompQhIso (SiteAbelianSheafCat (J.over A)))
        (additiveFunctorTotalRightDerived F)).app I
  -- Proof comment: the Chapter 19 cochain-level unit is defined by this exact composite, so the
  -- component at a K-injective complex inherits invertibility from the objectwise comparison iso.
  simpa [e, additiveFunctorTotalRightDerived, additiveFunctorTotalRightDerivedUnit,
    F, QhA, QhB, QA, QB, η, eSource, Category.assoc] using
    (show IsIso e.hom from inferInstance)

/-- Helper for Lemma 21.21.1: fix a functorial K-injective replacement on cochain complexes of
slice-site abelian sheaves over `A`. -/
private noncomputable abbrev relocalizationKInjectiveResolution
    (A : C) :
    CochainComplex.FunctorialComplexApproximation (SiteAbelianSheafCat (J.over A)) :=
  Classical.choose (CochainComplex.exists_functorial_kInjective_resolution
    (SiteAbelianSheafCat (J.over A)))

/-- Helper for Lemma 21.21.1: the chosen functorial replacement lands in K-injective complexes. -/
private theorem relocalizationKInjectiveResolution_isKInjective
    (A : C)
    (K : CochainComplex (SiteAbelianSheafCat (J.over A)) ℤ) :
    ((relocalizationKInjectiveResolution J A).toFunctor.obj K).IsKInjective := by
  -- Proof comment: the functorial replacement theorem records K-injectivity objectwise for the
  -- chosen approximation on the slice site over `A`.
  exact
    (Classical.choose_spec
      (CochainComplex.exists_functorial_kInjective_resolution
        (SiteAbelianSheafCat (J.over A)))).2 K

/-- Helper for Lemma 21.21.1: the chosen functorial replacement map is a quasi-isomorphism. -/
private theorem relocalizationKInjectiveResolution_quasiIso
    (A : C)
    (K : CochainComplex (SiteAbelianSheafCat (J.over A)) ℤ) :
    QuasiIso ((relocalizationKInjectiveResolution J A).ι.app K) := by
  -- Proof comment: the same approximation package supplies the comparison morphism as a
  -- quasi-isomorphism.
  exact (relocalizationKInjectiveResolution J A).quasiIso_app K

private theorem overMapPullback_mapDerivedCategory_isLeftDerivedFunctor
    {A B : C} (q : A ⟶ B)
    [Functor.Additive (J.overMapPullback AddCommGrpCat.{u} q)]
    [PreservesFiniteLimits (J.overMapPullback AddCommGrpCat.{u} q)]
    [PreservesFiniteColimits (J.overMapPullback AddCommGrpCat.{u} q)] :
    (J.overMapPullback AddCommGrpCat.{u} q).mapDerivedCategory.IsLeftDerivedFunctor
      ((J.overMapPullback AddCommGrpCat.{u} q).mapDerivedCategoryFactors.hom)
      (HomologicalComplex.quasiIso
        (SiteAbelianSheafCat (J.over B))
        (ComplexShape.up ℤ)) := by
  simpa using
    (Functor.isLeftDerivedFunctor_of_inverts
      (HomologicalComplex.quasiIso
        (SiteAbelianSheafCat (J.over B))
        (ComplexShape.up ℤ))
      ((J.overMapPullback AddCommGrpCat.{u} q).mapDerivedCategory)
      ((J.overMapPullback AddCommGrpCat.{u} q).mapDerivedCategoryFactors))

private theorem overMapPushforward_additiveFunctorTotalRightDerived_isRightDerivedFunctor
    {A B : C} (q : A ⟶ B)
    [∀ F : (Over A)ᵒᵖ ⥤ AddCommGrpCat.{u}, (Over.map q).op.HasPointwiseRightKanExtension F]
    [Functor.Additive
      ((Over.map q).sheafPushforwardCocontinuous
        AddCommGrpCat.{u} (J.over A) (J.over B))] :
    (additiveFunctorTotalRightDerived
        ((Over.map q).sheafPushforwardCocontinuous
          AddCommGrpCat.{u} (J.over A) (J.over B))).IsRightDerivedFunctor
    (additiveFunctorTotalRightDerivedUnit
        ((Over.map q).sheafPushforwardCocontinuous
          AddCommGrpCat.{u} (J.over A) (J.over B)))
      (HomologicalComplex.quasiIso
        (SiteAbelianSheafCat (J.over A))
        (ComplexShape.up ℤ)) := by
  -- TODO: unfold the Chapter 19 owner only far enough to align the concrete comparison
  -- `additiveFunctorTotalRightDerivedUnit` with the abstract `Functor.totalRightDerivedUnit`
  -- expected by the `IsRightDerivedFunctor` instance. The current direct `infer_instance`
  -- path no longer closes after the owner surface shifted through the homotopy-category model.
  sorry

private theorem overMapPullback_pushforwardDerived_comp_isLeftDerivedFunctor
    {A B : C} (q : A ⟶ B)
    [Functor.Additive (J.overMapPullback AddCommGrpCat.{u} q)]
    [PreservesFiniteLimits (J.overMapPullback AddCommGrpCat.{u} q)]
    [PreservesFiniteColimits (J.overMapPullback AddCommGrpCat.{u} q)]
    [∀ F : (Over A)ᵒᵖ ⥤ AddCommGrpCat.{u}, (Over.map q).op.HasPointwiseRightKanExtension F]
    [Functor.Additive
      ((Over.map q).sheafPushforwardCocontinuous
        AddCommGrpCat.{u} (J.over A) (J.over B))] :
    let L := (J.overMapPullback AddCommGrpCat.{u} q).mapDerivedCategory
    let R :=
      additiveFunctorTotalRightDerived
        ((Over.map q).sheafPushforwardCocontinuous
          AddCommGrpCat.{u} (J.over A) (J.over B))
    (L ⋙ R).IsLeftDerivedFunctor
      ((Functor.associator
          (DerivedCategory.Q :
            CochainComplex (SiteAbelianSheafCat (J.over B)) ℤ ⥤
              DerivedCategory (SiteAbelianSheafCat (J.over B)))
          L
          R).inv ≫
        Functor.whiskerRight
          ((J.overMapPullback AddCommGrpCat.{u} q).mapDerivedCategoryFactors.hom)
          R)
      (HomologicalComplex.quasiIso
        (SiteAbelianSheafCat (J.over B))
        (ComplexShape.up ℤ)) := by
  let L := (J.overMapPullback AddCommGrpCat.{u} q).mapDerivedCategory
  let R :=
    additiveFunctorTotalRightDerived
      ((Over.map q).sheafPushforwardCocontinuous
        AddCommGrpCat.{u} (J.over A) (J.over B))
  let e :
      (DerivedCategory.Q :
          CochainComplex (SiteAbelianSheafCat (J.over B)) ℤ ⥤
            DerivedCategory (SiteAbelianSheafCat (J.over B))) ⋙ (L ⋙ R) ≅
        (((J.overMapPullback AddCommGrpCat.{u} q).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
            (DerivedCategory.Q :
              CochainComplex (SiteAbelianSheafCat (J.over A)) ℤ ⥤
                DerivedCategory (SiteAbelianSheafCat (J.over A)))) ⋙
          R :=
    (Functor.associator
      (DerivedCategory.Q :
        CochainComplex (SiteAbelianSheafCat (J.over B)) ℤ ⥤
          DerivedCategory (SiteAbelianSheafCat (J.over B)))
      L
      R).symm ≪≫
      Functor.isoWhiskerRight
        ((J.overMapPullback AddCommGrpCat.{u} q).mapDerivedCategoryFactors)
        R
  -- Proof comment: the exact pullback owner already inverts quasi-isomorphisms, so the composite
  -- with the derived pushforward is a left derived functor of the displayed source.
  simpa [L, R, e] using
    (Functor.isLeftDerivedFunctor_of_inverts
      (HomologicalComplex.quasiIso
        (SiteAbelianSheafCat (J.over B))
        (ComplexShape.up ℤ))
      (L ⋙ R)
      e)

private theorem overMapPushforward_pullbackDerived_comp_isRightDerivedFunctor
    {A B : C} (q : A ⟶ B)
    [Functor.Additive (J.overMapPullback AddCommGrpCat.{u} q)]
    [PreservesFiniteLimits (J.overMapPullback AddCommGrpCat.{u} q)]
    [PreservesFiniteColimits (J.overMapPullback AddCommGrpCat.{u} q)]
    [∀ F : (Over A)ᵒᵖ ⥤ AddCommGrpCat.{u}, (Over.map q).op.HasPointwiseRightKanExtension F]
    [Functor.Additive
      ((Over.map q).sheafPushforwardCocontinuous
        AddCommGrpCat.{u} (J.over A) (J.over B))] :
    let R :=
      additiveFunctorTotalRightDerived
        ((Over.map q).sheafPushforwardCocontinuous
          AddCommGrpCat.{u} (J.over A) (J.over B))
    let L := (J.overMapPullback AddCommGrpCat.{u} q).mapDerivedCategory
    (R ⋙ L).IsRightDerivedFunctor
      (Functor.whiskerRight
          (additiveFunctorTotalRightDerivedUnit
            ((Over.map q).sheafPushforwardCocontinuous
              AddCommGrpCat.{u} (J.over A) (J.over B)))
          L ≫
        (Functor.associator
          (DerivedCategory.Q :
            CochainComplex (SiteAbelianSheafCat (J.over A)) ℤ ⥤
              DerivedCategory (SiteAbelianSheafCat (J.over A)))
          R
          L).hom)
        (HomologicalComplex.quasiIso
          (SiteAbelianSheafCat (J.over A))
          (ComplexShape.up ℤ)) := by
  -- TODO: replan should either supply the exported postcomposition instance for right derived
  -- functors by exact target functors or replace this step with an explicit uniqueness argument.
  sorry

private noncomputable def overMapPullbackDerived_pushforwardAdjunction
    {A B : C} (q : A ⟶ B)
    [Functor.Additive (J.overMapPullback AddCommGrpCat.{u} q)]
    [PreservesFiniteLimits (J.overMapPullback AddCommGrpCat.{u} q)]
    [PreservesFiniteColimits (J.overMapPullback AddCommGrpCat.{u} q)]
    [∀ F : (Over A)ᵒᵖ ⥤ AddCommGrpCat.{u}, (Over.map q).op.HasPointwiseRightKanExtension F]
    [Functor.Additive
      ((Over.map q).sheafPushforwardCocontinuous
        AddCommGrpCat.{u} (J.over A) (J.over B))] :
    (J.overMapPullback AddCommGrpCat.{u} q).mapDerivedCategory ⊣
      additiveFunctorTotalRightDerived
        ((Over.map q).sheafPushforwardCocontinuous
          AddCommGrpCat.{u} (J.over A) (J.over B)) := by
  let L := (J.overMapPullback AddCommGrpCat.{u} q).mapDerivedCategory
  let R :=
    additiveFunctorTotalRightDerived
      ((Over.map q).sheafPushforwardCocontinuous
        AddCommGrpCat.{u} (J.over A) (J.over B))
  let _ :
      L.IsLeftDerivedFunctor
        ((J.overMapPullback AddCommGrpCat.{u} q).mapDerivedCategoryFactors.hom)
        (HomologicalComplex.quasiIso
          (SiteAbelianSheafCat (J.over B))
          (ComplexShape.up ℤ)) :=
    overMapPullback_mapDerivedCategory_isLeftDerivedFunctor J q
  let _ :
      R.IsRightDerivedFunctor
        (additiveFunctorTotalRightDerivedUnit
          ((Over.map q).sheafPushforwardCocontinuous
            AddCommGrpCat.{u} (J.over A) (J.over B)))
        (HomologicalComplex.quasiIso
          (SiteAbelianSheafCat (J.over A))
          (ComplexShape.up ℤ)) :=
    overMapPushforward_additiveFunctorTotalRightDerived_isRightDerivedFunctor J q
  let _ :
      (L ⋙ R).IsLeftDerivedFunctor
        ((Functor.associator
            (DerivedCategory.Q :
              CochainComplex (SiteAbelianSheafCat (J.over B)) ℤ ⥤
                DerivedCategory (SiteAbelianSheafCat (J.over B)))
            L
            R).inv ≫
          Functor.whiskerRight
            ((J.overMapPullback AddCommGrpCat.{u} q).mapDerivedCategoryFactors.hom)
            R)
        (HomologicalComplex.quasiIso
          (SiteAbelianSheafCat (J.over B))
          (ComplexShape.up ℤ)) := by
    simpa [L, R] using
      overMapPullback_pushforwardDerived_comp_isLeftDerivedFunctor J q
  let _ :
      (R ⋙ L).IsRightDerivedFunctor
        (Functor.whiskerRight
            (additiveFunctorTotalRightDerivedUnit
              ((Over.map q).sheafPushforwardCocontinuous
                AddCommGrpCat.{u} (J.over A) (J.over B)))
            L ≫
          (Functor.associator
            (DerivedCategory.Q :
              CochainComplex (SiteAbelianSheafCat (J.over A)) ℤ ⥤
                DerivedCategory (SiteAbelianSheafCat (J.over A)))
            R
            L).hom)
        (HomologicalComplex.quasiIso
          (SiteAbelianSheafCat (J.over A))
          (ComplexShape.up ℤ)) := by
    simpa [L, R] using
      overMapPushforward_pullbackDerived_comp_isRightDerivedFunctor J q
  exact
    Adjunction.derived
      (CategoryTheory.Adjunction.mapHomologicalComplex
        ((Over.map q).sheafAdjunctionCocontinuous
          AddCommGrpCat.{u} (J.over A) (J.over B))
        (ComplexShape.up ℤ))
      (HomologicalComplex.quasiIso
        (SiteAbelianSheafCat (J.over B))
        (ComplexShape.up ℤ))
      (HomologicalComplex.quasiIso
        (SiteAbelianSheafCat (J.over A))
        (ComplexShape.up ℤ))
      ((J.overMapPullback AddCommGrpCat.{u} q).mapDerivedCategoryFactors.hom)
      (additiveFunctorTotalRightDerivedUnit
        ((Over.map q).sheafPushforwardCocontinuous
          AddCommGrpCat.{u} (J.over A) (J.over B)))

/-- Helper for Lemma 21.21.1: the canonical mate of the derived relocalization pullback square is
the natural transformation from `Rj_{X/Y,*} ⋙ j_{Y'/Y}^{-1}` to
`j_{X'/X}^{-1} ⋙ Rj_{X'/Y',*}`. -/
private noncomputable def relocalizationDerivedBaseChangeNatTrans
    (hcart : IsPullback i p f g) :
    (additiveFunctorTotalRightDerived
        ((Over.map f).sheafPushforwardCocontinuous
          AddCommGrpCat.{u} (J.over X) (J.over Y)) ⋙
      (J.overMapPullback AddCommGrpCat.{u} g).mapDerivedCategory) ⟶
      ((J.overMapPullback AddCommGrpCat.{u} i).mapDerivedCategory ⋙
        additiveFunctorTotalRightDerived
          ((Over.map p).sheafPushforwardCocontinuous
            AddCommGrpCat.{u} (J.over X') (J.over Y'))) :=
  -- Proof comment: apply `mateEquiv` to the derived pullback square
  -- `Lg ⋙ Lp ≅ Lf ⋙ Li`, using the derived adjunctions for `f` and `p`.
  ((mateEquiv
      (overMapPullbackDerived_pushforwardAdjunction J f)
      (overMapPullbackDerived_pushforwardAdjunction J p))
      (TwoSquare.mk
        (J.overMapPullback AddCommGrpCat.{u} g).mapDerivedCategory
        (J.overMapPullback AddCommGrpCat.{u} f).mapDerivedCategory
        (J.overMapPullback AddCommGrpCat.{u} p).mapDerivedCategory
        (J.overMapPullback AddCommGrpCat.{u} i).mapDerivedCategory
        (relocalizationDerivedSquareIso J i p f g hcart).hom)).natTrans

/-- Helper for Lemma 21.21.1: the mate comparison constructed above is exactly the canonical
`derivedBaseChangeMap` componentwise. -/
private theorem relocalizationDerivedBaseChangeNatTrans_app_eq_derivedBaseChangeMap
    (hcart : IsPullback i p f g)
    (K : DAb[X]) :
    (relocalizationDerivedBaseChangeNatTrans J i p f g hcart).app K =
      derivedBaseChangeMap
        ((J.overMapPullback AddCommGrpCat.{u} f).mapDerivedCategory)
        ((J.overMapPullback AddCommGrpCat.{u} p).mapDerivedCategory)
        ((J.overMapPullback AddCommGrpCat.{u} g).mapDerivedCategory)
        ((J.overMapPullback AddCommGrpCat.{u} i).mapDerivedCategory)
        (additiveFunctorTotalRightDerived
          ((Over.map f).sheafPushforwardCocontinuous
            AddCommGrpCat.{u} (J.over X) (J.over Y)))
        (additiveFunctorTotalRightDerived
          ((Over.map p).sheafPushforwardCocontinuous
            AddCommGrpCat.{u} (J.over X') (J.over Y')))
        (overMapPullbackDerived_pushforwardAdjunction J f)
        (overMapPullbackDerived_pushforwardAdjunction J p)
        (relocalizationDerivedSquareIso J i p f g hcart)
        K := by
  -- TODO: once the derived adjunction route is stabilized, show that the chosen mate comparison
  -- satisfies `IsDerivedBaseChangeMap` and then conclude with
  -- `IsDerivedBaseChangeMap.eq_derivedBaseChangeMap`. The current blocker is the unresolved
  -- derived-adjunction scaffold behind `overMapPullbackDerived_pushforwardAdjunction`.
  sorry

/-- Helper for Lemma 21.21.1: the derived mate comparison is an isomorphism at each object of
`D(𝒞/X)`. -/
private theorem relocalizationDerivedBaseChangeNatTrans_app_isIso
    (hcart : IsPullback i p f g)
    (K : DAb[X]) :
    IsIso ((relocalizationDerivedBaseChangeNatTrans J i p f g hcart).app K) := by
  sorry

/-- Lemma 21.21.1: for a cartesian square
`X' ⟶ X`
`↓     ↓`
`Y' ⟶ Y`
in a site `𝒞`, inverse image along `Y' ⟶ Y` commutes with the derived direct image along
`X ⟶ Y` after relocalization: the two composite functors
`j_{Y'/Y}^{-1} ∘ Rj_{X/Y, *}` and `Rj_{X'/Y', *} ∘ j_{X'/X}^{-1}` from `D(𝒞/X)` to
`D(𝒞/Y')` are canonically isomorphic. -/
@[stacks 0EZ0]
theorem relocalization_rightDerived_pushforward_inverse_image_isomorphic
    (hcart : IsPullback i p f g) :
    IsIsomorphic
      (additiveFunctorTotalRightDerived
          ((Over.map f).sheafPushforwardCocontinuous
            AddCommGrpCat.{u} (J.over X) (J.over Y)) ⋙
        (J.overMapPullback AddCommGrpCat.{u} g).mapDerivedCategory)
      ((J.overMapPullback AddCommGrpCat.{u} i).mapDerivedCategory ⋙
        additiveFunctorTotalRightDerived
          ((Over.map p).sheafPushforwardCocontinuous
            AddCommGrpCat.{u} (J.over X') (J.over Y'))) := by
  -- Proof comment: once every component of the canonical mate comparison is an isomorphism, the
  -- whole natural transformation is an isomorphism and therefore packages the desired
  -- functor-level `IsIsomorphic` statement.
  let τ := relocalizationDerivedBaseChangeNatTrans J i p f g hcart
  letI : IsIso τ := by
    exact
      (NatTrans.isIso_iff_isIso_app τ).2
        (fun K ↦ relocalizationDerivedBaseChangeNatTrans_app_isIso J i p f g hcart K)
  exact ⟨asIso τ⟩

/-- Objectwise companion to Lemma 21.21.1: the canonical derived base-change morphism
`j_{Y'/Y}^{-1} (Rj_{X/Y, *} K) ⟶ Rj_{X'/Y', *} (j_{X'/X}^{-1} K)` is an isomorphism for every
`K : D(𝒞/X)`. -/
theorem relocalization_rightDerived_pushforward_inverse_image_app_isIso
    (hcart : IsPullback i p f g)
    (K : DAb[X]) :
    IsIso
      (derivedBaseChangeMap
        ((J.overMapPullback AddCommGrpCat.{u} f).mapDerivedCategory)
        ((J.overMapPullback AddCommGrpCat.{u} p).mapDerivedCategory)
        ((J.overMapPullback AddCommGrpCat.{u} g).mapDerivedCategory)
        ((J.overMapPullback AddCommGrpCat.{u} i).mapDerivedCategory)
        (additiveFunctorTotalRightDerived
          ((Over.map f).sheafPushforwardCocontinuous
            AddCommGrpCat.{u} (J.over X) (J.over Y)))
        (additiveFunctorTotalRightDerived
          ((Over.map p).sheafPushforwardCocontinuous
            AddCommGrpCat.{u} (J.over X') (J.over Y')))
        (overMapPullbackDerived_pushforwardAdjunction J f)
        (overMapPullbackDerived_pushforwardAdjunction J p)
        (relocalizationDerivedSquareIso J i p f g hcart)
        K) := by
  -- Proof comment: rewrite the source-facing base-change morphism to the canonical mate
  -- comparison and then reuse the objectwise isomorphism statement for that mate.
  rw [← relocalizationDerivedBaseChangeNatTrans_app_eq_derivedBaseChangeMap
    (J := J) (i := i) (p := p) (f := f) (g := g) hcart K]
  exact relocalizationDerivedBaseChangeNatTrans_app_isIso J i p f g hcart K

end

end CategoryTheory
