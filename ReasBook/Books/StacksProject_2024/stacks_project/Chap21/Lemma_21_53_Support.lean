import StacksProject_2024.Chap18.Definition_18_43_1
import StacksProject_2024.Chap21.SheafModuleDerivedRestriction

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))]

/-- A family of additive constant-sheaf functors on slice sites yields the pointwise instance. -/
instance constantSheafOverAdditiveOfFamily
    [h : ∀ U : C, (constantSheaf (J.over U) (ModuleCat.{w} Λ)).Additive] (U : C) :
    (constantSheaf (J.over U) (ModuleCat.{w} Λ)).Additive :=
  h U

/-- A family of slice-site constant-sheaf functors preserving finite limits yields the pointwise
instance. -/
instance constantSheafOverPreservesFiniteLimitsOfFamily
    [h : ∀ U : C, PreservesFiniteLimits (constantSheaf (J.over U) (ModuleCat.{w} Λ))] (U : C) :
    PreservesFiniteLimits (constantSheaf (J.over U) (ModuleCat.{w} Λ)) :=
  h U

/-- A family of slice-site constant-sheaf functors preserving finite colimits yields the pointwise
instance. -/
instance constantSheafOverPreservesFiniteColimitsOfFamily
    [h : ∀ U : C, PreservesFiniteColimits (constantSheaf (J.over U) (ModuleCat.{w} Λ))] (U : C) :
    PreservesFiniteColimits (constantSheaf (J.over U) (ModuleCat.{w} Λ)) :=
  h U

end

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))]
variable [CategoryWithHomology (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, CategoryWithHomology (Sheaf (J.over U) (ModuleCat.{w} Λ))]
variable [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective (ModuleCat.{w} Λ)]
variable [(constantSheaf J (ModuleCat.{w} Λ)).Additive]
variable [PreservesFiniteLimits (constantSheaf J (ModuleCat.{w} Λ))]
variable [PreservesFiniteColimits (constantSheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, (constantSheaf (J.over U) (ModuleCat.{w} Λ)).Additive]
variable [∀ U : C, PreservesFiniteLimits (constantSheaf (J.over U) (ModuleCat.{w} Λ))]
variable [∀ U : C, PreservesFiniteColimits (constantSheaf (J.over U) (ModuleCat.{w} Λ))]
variable [∀ U : C, (J.overPullback (ModuleCat.{w} Λ) U).Additive]
variable [∀ U : C, PreservesFiniteLimits (J.overPullback (ModuleCat.{w} Λ) U)]
variable [∀ U : C, PreservesFiniteColimits (J.overPullback (ModuleCat.{w} Λ) U)]

/-- Restricting the constant-sheaf functor to a slice site agrees canonically with the constant
sheaf functor on that slice site. -/
noncomputable def constantSheafOverIso (U : C) :
    constantSheaf J (ModuleCat.{w} Λ) ⋙ J.overPullback (ModuleCat.{w} Λ) U ≅
      constantSheaf (J.over U) (ModuleCat.{w} Λ) :=
  NatIso.ofComponents
    (fun M ↦ constantSheafOverObjIso (J := J) (D := ModuleCat.{w} Λ) U M)
    (by
      intro M N f
      apply (sheafToPresheaf (J.over U) (ModuleCat.{w} Λ)).map_injective
      let cM :=
        constant_presheaf_over_comparison (J := J) (D := ModuleCat.{w} Λ) U M
      let cN :=
        constant_presheaf_over_comparison (J := J) (D := ModuleCat.{w} Λ) U N
      let g :
          (((constantSheaf J (ModuleCat.{w} Λ)).obj M).over U).obj ⟶
            (((constantSheaf J (ModuleCat.{w} Λ)).obj N).over U).obj :=
        ((J.overPullback (ModuleCat.{w} Λ) U).map
          ((constantSheaf J (ModuleCat.{w} Λ)).map f)).1
      have hg :
          g ≫ toSheafify (J.over U) (((constantSheaf J (ModuleCat.{w} Λ)).obj N).over U).obj =
            toSheafify (J.over U) (((constantSheaf J (ModuleCat.{w} Λ)).obj M).over U).obj ≫
              sheafifyMap (J := J.over U) g := by
        simpa [g] using toSheafify_naturality (J := J.over U) g
      have hc_presheaf :
          ((Functor.const (Over U)ᵒᵖ).map f) ≫ cN = cM ≫ g := by
        change (Over.forget U).op.whiskerLeft
            (((Functor.const Cᵒᵖ).map f) ≫ toSheafify J ((Functor.const Cᵒᵖ).obj N)) =
          (Over.forget U).op.whiskerLeft
            (toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫
              sheafifyMap J ((Functor.const Cᵒᵖ).map f))
        exact congrArg (Functor.whiskerLeft (Over.forget U).op)
          (toSheafify_naturality (J := J) ((Functor.const Cᵒᵖ).map f))
      have hWcM : (J.over U).W cM :=
        constant_presheaf_over_comparison_is_W (J := J) (D := ModuleCat.{w} Λ)
          (FD := fun X Y : ModuleCat.{w} Λ ↦ X →ₗ[Λ] Y) (CD := fun X ↦ X) U M
      have hWcN : (J.over U).W cN :=
        constant_presheaf_over_comparison_is_W (J := J) (D := ModuleCat.{w} Λ)
          (FD := fun X Y : ModuleCat.{w} Λ ↦ X →ₗ[Λ] Y) (CD := fun X ↦ X) U N
      have hIsoCMapM :
          IsIso ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cM) :=
        ((J.over U).W_iff (A := ModuleCat.{w} Λ) cM).mp hWcM
      let eM :
          (constantSheaf (J.over U) (ModuleCat.{w} Λ)).obj M ≅
            (presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).obj
              ((((constantSheaf J (ModuleCat.{w} Λ)).obj M).over U).obj) :=
        @asIso _ _ _ _
          ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cM) hIsoCMapM
      letI : IsIso ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cM) := hIsoCMapM
      letI : IsIso (sheafifyMap (J := J.over U) cM) := by
        have hIsoPresheaf :
            IsIso ((sheafToPresheaf (J.over U) (ModuleCat.{w} Λ)).map eM.hom) := by
          infer_instance
        simpa [eM, CategoryTheory.sheafifyMap] using hIsoPresheaf
      have hIsoCMapN :
          IsIso ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cN) :=
        ((J.over U).W_iff (A := ModuleCat.{w} Λ) cN).mp hWcN
      letI :
          IsIso ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map
            (constant_presheaf_over_comparison (J := J) (D := ModuleCat.{w} Λ) U M)) := by
        simpa [cM] using hIsoCMapM
      letI :
          IsIso ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map
            (constant_presheaf_over_comparison (J := J) (D := ModuleCat.{w} Λ) U N)) := by
        simpa [cN] using hIsoCMapN
      let eN :
          (constantSheaf (J.over U) (ModuleCat.{w} Λ)).obj N ≅
            (presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).obj
              ((((constantSheaf J (ModuleCat.{w} Λ)).obj N).over U).obj) :=
        @asIso _ _ _ _
          ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cN) hIsoCMapN
      letI : IsIso ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cN) := hIsoCMapN
      letI : IsIso (sheafifyMap (J := J.over U) cN) := by
        have hIsoPresheaf :
            IsIso ((sheafToPresheaf (J.over U) (ModuleCat.{w} Λ)).map eN.hom) := by
          infer_instance
        simpa [eN, CategoryTheory.sheafifyMap] using hIsoPresheaf
      have hc :
          inv ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cM).hom ≫
              ((constantSheaf (J.over U) (ModuleCat.{w} Λ)).map f).hom ≫
                ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cN).hom =
            ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map g).hom := by
        have hMap :
            ((constantSheaf (J.over U) (ModuleCat.{w} Λ)).map f).hom ≫
                ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cN).hom =
              ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cM).hom ≫
                ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map g).hom := by
          simpa [constantSheaf, Category.assoc] using
            congrArg
              (fun α ↦ α.hom)
              (congrArg (Functor.map (presheafToSheaf (J.over U) (ModuleCat.{w} Λ))) hc_presheaf)
        calc
          inv ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cM).hom ≫
              ((constantSheaf (J.over U) (ModuleCat.{w} Λ)).map f).hom ≫
                ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cN).hom =
              inv ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cM).hom ≫
                ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cM).hom ≫
                  ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map g).hom := by
            simpa [Category.assoc] using
              congrArg
                (fun α ↦ inv ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cM).hom ≫ α)
                hMap
          _ = ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map g).hom := by
            simp
      apply
        (cancel_mono (((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cN).hom)).1
      suffices hGoal :
          (toSheafify (J.over U)
                ((J.overPullback (ModuleCat.{w} Λ) U).obj
                  ((constantSheaf J (ModuleCat.{w} Λ)).obj M)).obj ≫
                ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map
                    ((J.overPullback (ModuleCat.{w} Λ) U).map
                      ((constantSheaf J (ModuleCat.{w} Λ)).map f)).hom).hom ≫
                  inv ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cN).hom) ≫
              ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cN).hom =
          (toSheafify (J.over U)
                ((J.overPullback (ModuleCat.{w} Λ) U).obj
                  ((constantSheaf J (ModuleCat.{w} Λ)).obj M)).obj ≫
              inv ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cM).hom ≫
                ((constantSheaf (J.over U) (ModuleCat.{w} Λ)).map f).hom) ≫
            ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cN).hom by
        have hInvHomCMapM :
            (inv ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cM)).hom =
              inv ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cM).hom := by
          apply IsIso.eq_inv_of_hom_inv_id
          exact congrArg (fun α ↦ α.hom) (IsIso.hom_inv_id ((presheafToSheaf (J.over U)
            (ModuleCat.{w} Λ)).map cM))
        have hInvHomCMapN :
            (inv ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cN)).hom =
              inv ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cN).hom := by
          apply IsIso.eq_inv_of_hom_inv_id
          exact congrArg (fun α ↦ α.hom) (IsIso.hom_inv_id ((presheafToSheaf (J.over U)
            (ModuleCat.{w} Λ)).map cN))
        simpa [constantSheafOverObjIso, CategoryTheory.sheafifyMap, Category.assoc, cM, cN,
          ← hInvHomCMapM, ← hInvHomCMapN] using hGoal
      calc
        (toSheafify (J.over U)
              ((J.overPullback (ModuleCat.{w} Λ) U).obj
                ((constantSheaf J (ModuleCat.{w} Λ)).obj M)).obj ≫
              ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map
                  ((J.overPullback (ModuleCat.{w} Λ) U).map
                    ((constantSheaf J (ModuleCat.{w} Λ)).map f)).hom).hom ≫
                inv ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cN).hom) ≫
            ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cN).hom =
          toSheafify (J.over U)
              ((J.overPullback (ModuleCat.{w} Λ) U).obj
                ((constantSheaf J (ModuleCat.{w} Λ)).obj M)).obj ≫
            ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map g).hom := by
          simpa [g]
        _ =
          toSheafify (J.over U)
              ((J.overPullback (ModuleCat.{w} Λ) U).obj
                ((constantSheaf J (ModuleCat.{w} Λ)).obj M)).obj ≫
            (inv ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cM).hom ≫
              ((constantSheaf (J.over U) (ModuleCat.{w} Λ)).map f).hom ≫
                ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cN).hom) := by
          simpa [Category.assoc] using
            congrArg
              (fun α ↦
                toSheafify (J.over U)
                  ((J.overPullback (ModuleCat.{w} Λ) U).obj
                    ((constantSheaf J (ModuleCat.{w} Λ)).obj M)).obj ≫ α)
              hc.symm
        _ =
          (toSheafify (J.over U)
                ((J.overPullback (ModuleCat.{w} Λ) U).obj
                  ((constantSheaf J (ModuleCat.{w} Λ)).obj M)).obj ≫
              inv ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cM).hom ≫
                ((constantSheaf (J.over U) (ModuleCat.{w} Λ)).map f).hom) ≫
            ((presheafToSheaf (J.over U) (ModuleCat.{w} Λ)).map cN).hom := by
          simp [Category.assoc]
    )

/-- The canonical derived comparison between restricting an ambient constant derived object and the
constant derived object on the slice site. -/
noncomputable def constantSheafOverDerivedIso (U : C) :
    (constantSheaf J (ModuleCat.{w} Λ)).mapDerivedCategory ⋙
        (J.overPullback (ModuleCat.{w} Λ) U).mapDerivedCategory ≅
      (constantSheaf (J.over U) (ModuleCat.{w} Λ)).mapDerivedCategory := by
  let QModule :
      CochainComplex (ModuleCat.{w} Λ) ℤ ⥤ DerivedCategory (ModuleCat.{w} Λ) :=
    DerivedCategory.Q
  let QSheaf :
      CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ ⥤
        DerivedCategory (Sheaf J (ModuleCat.{w} Λ)) :=
    DerivedCategory.Q
  let QOver :
      CochainComplex (Sheaf (J.over U) (ModuleCat.{w} Λ)) ℤ ⥤
        DerivedCategory (Sheaf (J.over U) (ModuleCat.{w} Λ)) :=
    DerivedCategory.Q
  let eFactors :
      ((constantSheaf J (ModuleCat.{w} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QSheaf) ⋙
          (J.overPullback (ModuleCat.{w} Λ) U).mapDerivedCategory ≅
        (constantSheaf J (ModuleCat.{w} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (J.overPullback (ModuleCat.{w} Λ) U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            QOver :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        ((constantSheaf J (ModuleCat.{w} Λ)).mapHomologicalComplex (ComplexShape.up ℤ))
        (show QSheaf ⋙ (J.overPullback (ModuleCat.{w} Λ) U).mapDerivedCategory ≅
            (J.overPullback (ModuleCat.{w} Λ) U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
              QOver from
          (J.overPullback (ModuleCat.{w} Λ) U).mapDerivedCategoryFactors)
  let eCompare :
      (constantSheaf J (ModuleCat.{w} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (J.overPullback (ModuleCat.{w} Λ) U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QOver ≅
        (constantSheaf (J.over U) (ModuleCat.{w} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          QOver :=
    Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (constantSheafOverIso (J := J) (Λ := Λ) U) (ComplexShape.up ℤ))
      QOver
  letI :
      Localization.Lifting QModule
        (HomologicalComplex.quasiIso (ModuleCat.{w} Λ) (ComplexShape.up ℤ))
        (((constantSheaf J (ModuleCat.{w} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            QSheaf) ⋙
          (J.overPullback (ModuleCat.{w} Λ) U).mapDerivedCategory)
        ((constantSheaf J (ModuleCat.{w} Λ)).mapDerivedCategory ⋙
          (J.overPullback (ModuleCat.{w} Λ) U).mapDerivedCategory) :=
    Localization.Lifting.compRight
      QModule
      (HomologicalComplex.quasiIso (ModuleCat.{w} Λ) (ComplexShape.up ℤ))
      ((constantSheaf J (ModuleCat.{w} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QSheaf)
      (constantSheaf J (ModuleCat.{w} Λ)).mapDerivedCategory
      (J.overPullback (ModuleCat.{w} Λ) U).mapDerivedCategory
  exact Localization.liftNatIso
    QModule
    (HomologicalComplex.quasiIso (ModuleCat.{w} Λ) (ComplexShape.up ℤ))
    (((constantSheaf J (ModuleCat.{w} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QSheaf) ⋙
      (J.overPullback (ModuleCat.{w} Λ) U).mapDerivedCategory)
    ((constantSheaf (J.over U) (ModuleCat.{w} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      QOver)
    ((constantSheaf J (ModuleCat.{w} Λ)).mapDerivedCategory ⋙
      (J.overPullback (ModuleCat.{w} Λ) U).mapDerivedCategory)
    ((constantSheaf (J.over U) (ModuleCat.{w} Λ)).mapDerivedCategory)
    (eFactors ≪≫ eCompare)

end

end CategoryTheory.Sheaf
