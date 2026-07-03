import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_21_39_1_Category_over_point (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory

/-- Example 21.39.1 (Category over point): for a category `\mathcal C`, viewed with the chaotic
topology so that presheaves and sheaves agree, the `n`-th homology group of an abelian sheaf
`\mathcal F` on `\mathcal C` is the `n`-th left derived functor of taking colimits over
`\mathcal C^\mathrm{op}`. -/
abbrev categoryHomology {C : Type u} [Category.{v} C]
    [HasProjectiveResolutions (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]
    (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    AddCommGrpCat.{max u v} :=
  ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}).leftDerived n).obj ℱ

-- Proof sketch: unfold `categoryHomology`; it was defined to be the value of the `n`-th left
-- derived functor of the colimit functor on the abelian presheaf category `Cᵒᵖ ⥤ AddCommGrpCat`.
/-- The homology object of an abelian presheaf on `C` is, by definition, the value of the
`n`-th left derived functor of colimits over `Cᵒᵖ`. -/
theorem categoryHomology_eq_leftDerivedColimit {C : Type u} [Category.{v} C]
    [HasProjectiveResolutions (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]
    (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    categoryHomology ℱ n =
      ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}).leftDerived n).obj
        ℱ := sorry

end CategoryTheory

/-! ### Example_21_39_2_Computing_homology (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable [HasProjectiveResolutions (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]

/-- The category homology functor `H_n(\mathcal C, -)` on abelian presheaves is the `n`-th left
derived functor of the colimit functor on `Cᵒᵖ`. -/
abbrev categoryHomology (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    AddCommGrpCat.{max u v} :=
  ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}).leftDerived n).obj ℱ

-- Proof sketch: this is immediate from the definition of `categoryHomology` as the `n`-th left
-- derived colimit functor on abelian presheaves.
/-- Unfolding `categoryHomology` identifies it with the `n`-th left derived colimit. -/
theorem categoryHomology_eq_leftDerivedColimit (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    categoryHomology ℱ n =
      ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}).leftDerived n).obj
        ℱ := sorry

/-- The degree-zero category homology of an abelian presheaf is its ordinary colimit. -/
abbrev categoryHomology_zero_iso_colimit (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    categoryHomology ℱ 0 ≅
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}).obj ℱ :=
  ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}).leftDerivedZeroIsoSelf).app
    ℱ

/-- Example 21.39.2 (Computing homology): if `P` is a projective resolution of an abelian
presheaf `ℱ` on `C`, then applying colimits termwise to `P.complex` gives a chain complex whose
`n`-th homology computes `H_n(\mathcal C, \mathcal F)`. This is the categorical form of the
explicit complex `K_\bullet(\mathcal F)` described in the text. -/
abbrev categoryHomology_iso_homology_of_projectiveResolution
    (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (P : ProjectiveResolution ℱ) (n : ℕ) :
    categoryHomology ℱ n ≅
      (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).obj
        (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex) :=
  P.isoLeftDerivedObj
    (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}) n

-- Proof sketch: unfold `categoryHomology_iso_homology_of_projectiveResolution`; the displayed
-- isomorphism is exactly the standard projective-resolution computation isomorphism
-- `P.isoLeftDerivedObj` for the colimit functor.
/-- Unfolding the comparison isomorphism for category homology computed from `P` recovers the
standard projective-resolution isomorphism for the colimit functor. -/
theorem categoryHomology_iso_homology_of_projectiveResolution_def
    (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (P : ProjectiveResolution ℱ) (n : ℕ) :
    categoryHomology_iso_homology_of_projectiveResolution ℱ P n =
      P.isoLeftDerivedObj
        (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}) n := sorry

end

end CategoryTheory

/-! ### Example_21_39_3 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u₁ v₁

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C]
variable {C' : Type u₁} [Category.{v₁} C']
variable [HasProjectiveResolutions (Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁})]
variable [HasProjectiveResolutions (C'ᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁})]

/-- The abelian presheaf category on `C`, which is also the abelian sheaf category for the chaotic
topology on `C`. -/
private abbrev AbelianPresheafCat (C : Type u₁) [Category.{v₁} C] :=
  Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}

/-- The colimit functor whose left derived functors compute homology on a category. -/
private abbrev categoryHomologyColimitFunctor (C : Type u₁) [Category.{v₁} C] :
    AbelianPresheafCat C ⥤ AddCommGrpCat.{max u₁ v₁} :=
  colim

/-- The homology object `H_n(\mathcal C, \mathcal F)` of an abelian presheaf on `C`, defined as
the `n`-th left derived colimit over `Cᵒᵖ`. -/
abbrev categoryHomologyObject {C : Type u₁} [Category.{v₁} C]
    [HasProjectiveResolutions (Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁})]
    (ℱ : AbelianPresheafCat C) (n : ℕ) :
    AddCommGrpCat.{max u₁ v₁} :=
  ((categoryHomologyColimitFunctor C).leftDerived n).obj ℱ

-- Proof sketch: this is immediate from the definition of `categoryHomologyObject` as the
-- `n`-th left derived functor of the colimit functor.
/-- Unfolding `categoryHomologyObject` identifies it with the `n`-th left derived colimit. -/
theorem categoryHomologyObject_eq_leftDerivedColimit {C : Type u₁} [Category.{v₁} C]
    [HasProjectiveResolutions (Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁})]
    (ℱ : AbelianPresheafCat C) (n : ℕ) :
    categoryHomologyObject ℱ n =
      ((categoryHomologyColimitFunctor C).leftDerived n).obj ℱ := sorry

/-- Precomposition with `u.op`, i.e. the inverse-image functor on abelian sheaves for the chaotic
topology. -/
private abbrev categoryHomologyInverseImage (u : C' ⥤ C) :
    AbelianPresheafCat C ⥤ AbelianPresheafCat C' :=
  (Functor.whiskeringLeft (C'ᵒᵖ) (Cᵒᵖ) AddCommGrpCat.{max u₁ v₁}).obj u.op

/-- The natural comparison from the colimit over `C'` of `u^{-1}F` to the colimit over `C`. -/
private abbrev categoryHomologyColimitComparison (u : C' ⥤ C) :
    categoryHomologyInverseImage u ⋙ categoryHomologyColimitFunctor C' ⟶
    categoryHomologyColimitFunctor C where
  app F := colimit.pre F u.op
  naturality {F G} τ := by
    simpa [categoryHomologyInverseImage] using
      (colimit.pre_map τ u.op).symm

/-- Example 21.39.3: for a functor `u : \mathcal C' \to \mathcal C`, a morphism
`t : \mathcal F' \to u^{-1}\mathcal F`, and the canonical comparison map
`H_n(\mathcal C', u^{-1}\mathcal F) \to H_n(\mathcal C, \mathcal F)` coming from Remark 21.38.7,
there is an induced canonical map `H_n(\mathcal C', \mathcal F') \to H_n(\mathcal C, \mathcal F)`.
-/
abbrev categoryHomologyMap (u : C' ⥤ C)
    {ℱ : AbelianPresheafCat C} {ℱ' : AbelianPresheafCat C'}
    (t : ℱ' ⟶ (categoryHomologyInverseImage u).obj ℱ) (n : ℕ)
    (comparison :
      categoryHomologyObject ((categoryHomologyInverseImage u).obj ℱ) n ⟶
        categoryHomologyObject ℱ n) :
    categoryHomologyObject ℱ' n ⟶ categoryHomologyObject ℱ n :=
  ((categoryHomologyColimitFunctor C').leftDerived n).map t ≫ comparison

/-- Assuming precomposition with `u.op` preserves projective objects, this is the chain map on
projective-resolution complexes obtained by lifting `t` to the pulled-back resolution of
`\mathcal F` and then applying colimits termwise together with the canonical colimit comparison. -/
abbrev categoryHomologyComplexMap (u : C' ⥤ C)
    {ℱ : AbelianPresheafCat C} {ℱ' : AbelianPresheafCat C'}
    (t : ℱ' ⟶ (categoryHomologyInverseImage u).obj ℱ)
    [(categoryHomologyInverseImage u).PreservesProjectiveObjects]
    (P' : ProjectiveResolution ℱ') (P : ProjectiveResolution ℱ) :
    ((categoryHomologyColimitFunctor C').mapHomologicalComplex (ComplexShape.down ℕ)).obj
        P'.complex ⟶
      ((categoryHomologyColimitFunctor C).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        P.complex :=
  ((categoryHomologyColimitFunctor C').mapHomologicalComplex (ComplexShape.down ℕ)).map
      (ProjectiveResolution.lift t P'
        ((categoryHomologyInverseImage u).mapProjectiveResolution P)) ≫
    ((NatTrans.mapHomologicalComplex (categoryHomologyColimitComparison u)
      (ComplexShape.down ℕ)).app P.complex)

-- Proof sketch: unfold `categoryHomologyMap`; it is the composite of the map on the `n`-th left
-- derived colimit induced by `t` with the comparison map from `H_n(\mathcal C', u^{-1}\mathcal
-- F)` to `H_n(\mathcal C, \mathcal F)`.
/-- Unfolding `categoryHomologyMap` identifies it with the composite of the derived functorial map
on `t` with the chosen comparison map on homology. -/
theorem categoryHomologyMap_def
    (u : C' ⥤ C)
    {ℱ : AbelianPresheafCat C} {ℱ' : AbelianPresheafCat C'}
    (t : ℱ' ⟶ (categoryHomologyInverseImage u).obj ℱ)
    (n : ℕ)
    (comparison :
      categoryHomologyObject ((categoryHomologyInverseImage u).obj ℱ) n ⟶
        categoryHomologyObject ℱ n) :
    categoryHomologyMap u t n comparison =
      ((categoryHomologyColimitFunctor C').leftDerived n).map t ≫
        comparison := sorry

-- Proof sketch: this is immediate from the definition of `categoryHomologyComplexMap`.
/-- Unfolding `categoryHomologyComplexMap` gives the composite of the lifted map of projective
resolutions with the chain-level colimit comparison attached to `u`. -/
theorem categoryHomologyComplexMap_def
    (u : C' ⥤ C)
    {ℱ : AbelianPresheafCat C} {ℱ' : AbelianPresheafCat C'}
    (t : ℱ' ⟶ (categoryHomologyInverseImage u).obj ℱ)
    [(categoryHomologyInverseImage u).PreservesProjectiveObjects]
    (P' : ProjectiveResolution ℱ') (P : ProjectiveResolution ℱ) :
    categoryHomologyComplexMap u t P' P =
      ((categoryHomologyColimitFunctor C').mapHomologicalComplex (ComplexShape.down ℕ)).map
          (ProjectiveResolution.lift t P'
            ((categoryHomologyInverseImage u).mapProjectiveResolution P)) ≫
        ((NatTrans.mapHomologicalComplex (categoryHomologyColimitComparison u)
          (ComplexShape.down ℕ)).app P.complex) := sorry

end

end CategoryTheory

/-! ### Remark_21_39_4 (from Chap21) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section Generic

variable {C : Type u} [Category.{v} C]
variable {A : Type w} [Category.{max u v} A] [Abelian A]
variable [HasColimitsOfShape Cᵒᵖ A]

local notation "PresheafCat" => Cᵒᵖ ⥤ A
local notation "QisPresheaf" => HomotopyCategory.quasiIso PresheafCat (up ℤ)

/-- Evaluation of an `A`-valued presheaf on `C` at an object `U`. -/
private abbrev evaluatePresheafAt (U : C) : PresheafCat ⥤ A :=
  (evaluation (Cᵒᵖ) A).obj (Opposite.op U)

/-- The functor from the homotopy category of presheaf complexes to the derived category of `A`
obtained by taking colimits termwise. -/
private abbrev colimitToDerived :
    HomotopyCategory PresheafCat (up ℤ) ⥤ DerivedCategory A :=
  (colim : PresheafCat ⥤ A).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The total left derived functor of taking colimits of `A`-valued presheaf complexes. -/
private abbrev derivedColimit
    [Functor.HasLeftDerivedFunctor
      (colimitToDerived : HomotopyCategory PresheafCat (up ℤ) ⥤ DerivedCategory A)
      QisPresheaf] :
    DerivedCategory PresheafCat ⥤ DerivedCategory A :=
  colimitToDerived.totalLeftDerived DerivedCategory.Qh QisPresheaf

-- Proof sketch: this is the naturality relation for the universal colimit cocone, evaluated at
-- the vertex `op U`.
/-- The colimit cocone gives a natural transformation from evaluation at `U` to colimits. -/
private theorem evaluationToColimit_naturality (U : C)
    {𝒢 ℋ : PresheafCat} (τ : 𝒢 ⟶ ℋ) :
    (evaluatePresheafAt U).map τ ≫ colimit.ι ℋ (Opposite.op U) =
      colimit.ι 𝒢 (Opposite.op U) ≫ (colim : PresheafCat ⥤ A).map τ := sorry

/-- The natural transformation from evaluation at `U` to presheaf colimits. -/
private abbrev evaluationToColimitNatTrans (U : C) :
    evaluatePresheafAt U ⟶ (colim : PresheafCat ⥤ A) where
  app 𝒢 := colimit.ι 𝒢 (Opposite.op U)
  naturality := fun {_ _} τ ↦ evaluationToColimit_naturality U τ

/-- The comparison from derived evaluation at `U` to the underived colimit functor on homotopy
categories. -/
private abbrev evaluationDerivedComparison (U : C) :
    DerivedCategory.Qh ⋙ (evaluatePresheafAt U).mapDerivedCategory ⟶
      (colimitToDerived : HomotopyCategory PresheafCat (up ℤ) ⥤ DerivedCategory A) :=
  (evaluatePresheafAt U).mapDerivedCategoryFactorsh.hom ≫
    Functor.whiskerRight
      (NatTrans.mapHomotopyCategory (evaluationToColimitNatTrans U) (up ℤ))
      DerivedCategory.Qh

/-- The natural transformation from derived evaluation at `U` to the derived colimit functor. -/
private abbrev evaluationMapToDerivedColimit (U : C)
    [Functor.HasLeftDerivedFunctor
      (colimitToDerived : HomotopyCategory PresheafCat (up ℤ) ⥤ DerivedCategory A)
      QisPresheaf] :
    (evaluatePresheafAt U).mapDerivedCategory ⟶
      (derivedColimit : DerivedCategory PresheafCat ⥤ DerivedCategory A) :=
  let F : HomotopyCategory PresheafCat (up ℤ) ⥤ DerivedCategory A := colimitToDerived
  let LF : DerivedCategory PresheafCat ⥤ DerivedCategory A := derivedColimit
  LF.leftDerivedLift
    (F.totalLeftDerivedCounit DerivedCategory.Qh QisPresheaf)
    QisPresheaf
    ((evaluatePresheafAt U).mapDerivedCategory)
    (evaluationDerivedComparison U)

/-- The canonical morphism from the complex of sections over `U` to the derived colimit of a
complex of `A`-valued presheaves. -/
private abbrev sectionComplexToDerivedColimit (U : C) (K : CochainComplex PresheafCat ℤ)
    [Functor.HasLeftDerivedFunctor
      (colimitToDerived : HomotopyCategory PresheafCat (up ℤ) ⥤ DerivedCategory A)
      QisPresheaf] :
    DerivedCategory.Q.obj (((evaluatePresheafAt U).mapHomologicalComplex (up ℤ)).obj K) ⟶
      (derivedColimit : DerivedCategory PresheafCat ⥤ DerivedCategory A).obj
        (DerivedCategory.Q.obj K) :=
  (asIso ((evaluatePresheafAt U).mapDerivedCategoryFactors.hom.app K)).inv ≫
    (evaluationMapToDerivedColimit U).app (DerivedCategory.Q.obj K)

end Generic

section AddCommGrp

variable {C : Type u} [Category.{v} C]

local notation "AbPresheaf" => Cᵒᵖ ⥤ AddCommGrpCat
local notation "QisAbPresheaf" => HomotopyCategory.quasiIso AbPresheaf (up ℤ)
local notation "AbelianColimitToDerived" =>
  (colimitToDerived : HomotopyCategory AbPresheaf (up ℤ) ⥤ DerivedCategory AddCommGrpCat)

/-- Specialized derived colimit functor for abelian presheaves. -/
private abbrev abelianDerivedColimit
    [Functor.HasLeftDerivedFunctor AbelianColimitToDerived QisAbPresheaf] :
    DerivedCategory AbPresheaf ⥤ DerivedCategory AddCommGrpCat :=
  derivedColimit

/-- Remark 21.39.4: for an object `U` of `\mathcal C`, assuming the total left derived colimit
functor on complexes of abelian presheaves is defined, there is a canonical morphism from the
complex of sections `\mathcal F^\bullet(U)` to `L\pi_!(\mathcal F^\bullet)` in `D(\textit{Ab})`.
-/
noncomputable abbrev sectionComplexToLeftDerivedColimit (U : C)
    (K : CochainComplex AbPresheaf ℤ)
    [hLeft : Functor.HasLeftDerivedFunctor
      AbelianColimitToDerived
      QisAbPresheaf] :
    DerivedCategory.Q.obj (((evaluatePresheafAt U).mapHomologicalComplex (up ℤ)).obj K) ⟶
      (abelianDerivedColimit).obj (DerivedCategory.Q.obj K) :=
  let _ : Functor.HasLeftDerivedFunctor
      AbelianColimitToDerived QisAbPresheaf := hLeft
  sectionComplexToDerivedColimit U K

-- Proof sketch: after inserting the supplied left-derived-functor instance, this is exactly the
-- specialized generic construction of `sectionComplexToDerivedColimit`.
/-- The abelian-presheaf construction is the specialization of the generic derived-colimit map. -/
theorem sectionComplexToLeftDerivedColimit_def (U : C)
    (K : CochainComplex AbPresheaf ℤ)
    [hLeft : Functor.HasLeftDerivedFunctor AbelianColimitToDerived QisAbPresheaf] :
    sectionComplexToLeftDerivedColimit U K = sectionComplexToDerivedColimit U K := sorry

end AddCommGrp

section Module

variable {C : Type u} [Category.{v} C]
variable (B : Type w) [Ring B]

local notation "BPresheaf" => Cᵒᵖ ⥤ ModuleCat B
local notation "QisBPresheaf" => HomotopyCategory.quasiIso BPresheaf (up ℤ)
local notation "ModuleColimitToDerived" =>
  (colimitToDerived : HomotopyCategory BPresheaf (up ℤ) ⥤ DerivedCategory (ModuleCat B))

/-- Specialized derived colimit functor for module-valued presheaves. -/
private abbrev moduleDerivedColimit
    [Functor.HasLeftDerivedFunctor ModuleColimitToDerived QisBPresheaf] :
    DerivedCategory BPresheaf ⥤ DerivedCategory (ModuleCat B) :=
  derivedColimit

/-- The same construction as `sectionComplexToLeftDerivedColimit`, now for complexes of
presheaves of `B`-modules, with target in the derived category `D(B)`. -/
noncomputable abbrev moduleSectionComplexToLeftDerivedColimit (U : C)
    (K : CochainComplex BPresheaf ℤ)
    [hLeft : Functor.HasLeftDerivedFunctor
      ModuleColimitToDerived
      QisBPresheaf] :
    DerivedCategory.Q.obj (((evaluatePresheafAt U).mapHomologicalComplex (up ℤ)).obj K) ⟶
      (derivedColimit : DerivedCategory BPresheaf ⥤ DerivedCategory (ModuleCat B)).obj
        (DerivedCategory.Q.obj K) :=
  let _ : Functor.HasLeftDerivedFunctor
      ModuleColimitToDerived QisBPresheaf := hLeft
  sectionComplexToDerivedColimit U K

end Module

end CategoryTheory

/-! ### Lemma_21_39_5 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {A : Type w} [Category A] [Abelian A] [HasDerivedCategory A]
variable [HasDerivedCategory (Cᵒᵖ ⥤ A)]
variable [HasColimitsOfShape Cᵒᵖ A]

/-- The inverse-image functor for the projection from a category over a point is the constant
diagram functor. -/
abbrev categoryOverPointInverseImage : A ⥤ (Cᵒᵖ ⥤ A) :=
  (Functor.const (Cᵒᵖ) : A ⥤ (Cᵒᵖ ⥤ A))

/-- The constant inverse-image functor over a point is additive. -/
instance categoryOverPointInverseImage_additive :
    ((Functor.const (Cᵒᵖ) : A ⥤ (Cᵒᵖ ⥤ A))).Additive := sorry

/-- The exact inverse-image functor on derived categories for the projection from a category over a
point. -/
abbrev categoryOverPointDerivedInverseImage :
    DerivedCategory A ⥤ DerivedCategory (Cᵒᵖ ⥤ A) :=
  ((Functor.const (Cᵒᵖ) : A ⥤ (Cᵒᵖ ⥤ A))).mapDerivedCategory

/-- The lower shriek functor for the projection from a category over a point is the colimit
functor. -/
abbrev categoryOverPointLowerShriek : (Cᵒᵖ ⥤ A) ⥤ A :=
  colim

/-- The adjunction `\pi_! ⊣ \pi^{-1}` for the projection from a category over a point. -/
abbrev categoryOverPointLowerShriekAdjunction :
    (colim : (Cᵒᵖ ⥤ A) ⥤ A) ⊣ (Functor.const (Cᵒᵖ) : A ⥤ (Cᵒᵖ ⥤ A)) :=
  Limits.colimConstAdj

/-- The homotopy-to-derived functor whose total left derived functor is the derived lower shriek
for a category over a point. -/
abbrev categoryOverPointLowerShriekToDerived :
    HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤ DerivedCategory A :=
  ((colim : (Cᵒᵖ ⥤ A) ⥤ A)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- The derived lower shriek functor `L\pi_!` for the projection from a category over a point. -/
abbrev categoryOverPointDerivedLowerShriek
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointLowerShriekToDerived :
        HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤ DerivedCategory A)
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ))] :
    DerivedCategory (Cᵒᵖ ⥤ A) ⥤ DerivedCategory A :=
  Functor.totalLeftDerived
    (categoryOverPointLowerShriekToDerived :
      HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤ DerivedCategory A)
    (DerivedCategory.Qh :
      HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤
        DerivedCategory (Cᵒᵖ ⥤ A))
    (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ))

-- Proof sketch: if `C` has an initial object, then `Cᵒᵖ` has a terminal object, so the colimit of
-- a constant diagram is evaluation at that terminal object; if `C` has a final object, then
-- `Cᵒᵖ` has an initial object and the constant diagram still has colimit the given value because
-- all of its transition maps are identities.
/-- If the indexing category has an initial or a final object, then the underived lower shriek for
the projection to a point has invertible counit `\pi_! \pi^{-1} \to \mathrm{id}`. -/
theorem categoryOverPointLowerShriek_comp_inverseImage_counit_isIso
    (hC : Nonempty (Limits.HasInitial C) ∨ Nonempty (Limits.HasTerminal C)) :
    IsIso
      ((categoryOverPointLowerShriekAdjunction :
          (colim : (Cᵒᵖ ⥤ A) ⥤ A) ⊣ (Functor.const (Cᵒᵖ) : A ⥤ (Cᵒᵖ ⥤ A))).counit) := sorry

variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointLowerShriekToDerived :
    HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤ DerivedCategory A)
  (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ))]

-- Proof sketch: under the initial/final-object hypothesis, the underived composite
-- `π_! ∘ π⁻¹` has invertible counit by the previous theorem. Since `π⁻¹` is an exact functor, it
-- lifts directly to derived categories, and then the adjunction criterion of Lemma `4.24.4`
-- identifies invertibility of the derived counit with the statement that `Lπ_! ∘ π⁻¹ = id`.
/-- Lemma 21.39.5: in the category-over-a-point situation of Example 21.39.1, if `C` has either
an initial object or a final object, then the derived lower shriek followed by inverse image is
naturally isomorphic to the identity on `D(A)`, equivalently the counit
`L\pi_! \circ \pi^{-1} \to \mathrm{id}` is an isomorphism. Specializing `A` to `AddCommGrpCat`
and to `ModuleCat B` recovers the textbook statements on `D(\mathrm{Ab})` and `D(B)`. -/
theorem categoryOverPointDerivedLowerShriek_comp_inverseImage_counit_isIso
    (adj :
      (categoryOverPointDerivedLowerShriek :
          DerivedCategory (Cᵒᵖ ⥤ A) ⥤ DerivedCategory A) ⊣
        (categoryOverPointDerivedInverseImage :
          DerivedCategory A ⥤ DerivedCategory (Cᵒᵖ ⥤ A)))
    (hC : Nonempty (Limits.HasInitial C) ∨ Nonempty (Limits.HasTerminal C)) :
    IsIso adj.counit := sorry

end

end CategoryTheory

/-! ### Lemma_21_39_6 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {B : Type w} [CommRing B] {B' : Type w} [CommRing B']
variable [HasColimitsOfShape Cᵒᵖ (ModuleCat B)]
variable [HasColimitsOfShape Cᵒᵖ (ModuleCat B')]

local notation "BPresheaf" => Cᵒᵖ ⥤ ModuleCat B
local notation "BPrimePresheaf" => Cᵒᵖ ⥤ ModuleCat B'
local notation "QisB" => HomotopyCategory.quasiIso (ModuleCat B) (up ℤ)
local notation "QisBPresheaf" => HomotopyCategory.quasiIso BPresheaf (up ℤ)
local notation "QisBPrimePresheaf" => HomotopyCategory.quasiIso BPrimePresheaf (up ℤ)

/-- The functor `K(\mathcal A) ⥤ D(\mathcal B)` induced by an additive functor
`F : \mathcal A ⥤ \mathcal B`. -/
abbrev mapHomotopyCategoryToDerived
    {𝒜 : Type u} {ℬ : Type w}
    [Category.{v} 𝒜] [Category ℬ]
    [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory ℬ]
    (F : 𝒜 ⥤ ℬ) [F.Additive] :
    HomotopyCategory 𝒜 (up ℤ) ⥤ DerivedCategory ℬ :=
  F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The constant-diagram functor on `B`-modules is additive. -/
instance categoryOverPointDerivedInverseImage_additive :
    ((Functor.const (Cᵒᵖ) : ModuleCat B ⥤ BPresheaf)).Additive := sorry

/-- The exact inverse-image functor on derived categories for the projection from a category over a
point, here specialized to `B`-modules. -/
abbrev categoryOverPointDerivedInverseImage :
    DerivedCategory (ModuleCat B) ⥤ DerivedCategory BPresheaf :=
  (Functor.const (Cᵒᵖ) : ModuleCat B ⥤ BPresheaf).mapDerivedCategory

/-- The homotopy-to-derived functor whose total left derived functor is the derived lower shriek
for the projection from a category over a point. -/
abbrev categoryOverPointLowerShriekToDerived :
    HomotopyCategory BPresheaf (up ℤ) ⥤ DerivedCategory (ModuleCat B) :=
  (colim : BPresheaf ⥤ ModuleCat B).mapHomotopyCategory (up ℤ) ⋙
    DerivedCategory.Qh

/-- The derived lower shriek functor `L\pi_!` for the projection from a category over a point,
here specialized to `B`-modules. -/
abbrev categoryOverPointDerivedLowerShriek
    [Functor.HasLeftDerivedFunctor
      categoryOverPointLowerShriekToDerived
      QisBPresheaf] :
    DerivedCategory BPresheaf ⥤ DerivedCategory (ModuleCat B) :=
  Functor.totalLeftDerived
    categoryOverPointLowerShriekToDerived
    DerivedCategory.Qh
    QisBPresheaf

/-- Extension of scalars along a ring map `B → B'` is additive on module categories. -/
instance pointChangeOfRings_additive (φ : B →+* B') :
    (ModuleCat.extendScalars φ).Additive := sorry

/-- Pointwise extension of scalars along `φ` is additive on `B`-module valued presheaves. -/
instance presheafChangeOfRings_additive (φ : B →+* B') :
    ((Functor.whiskeringRight (Cᵒᵖ) (ModuleCat B) (ModuleCat B')).obj
      (ModuleCat.extendScalars φ)).Additive := sorry

/-- The derived inverse-image functor on `D(B)` attached to a ring map `B → B'`. -/
abbrev pointChangeOfRingsDerivedPullback (φ : B →+* B')
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived (ModuleCat.extendScalars φ))
      QisB] :
    DerivedCategory (ModuleCat B) ⥤ DerivedCategory (ModuleCat B') :=
  Functor.totalLeftDerived
    (mapHomotopyCategoryToDerived (ModuleCat.extendScalars φ))
    DerivedCategory.Qh
    QisB

-- Proof sketch: unfold `pointChangeOfRingsDerivedPullback`; it is defined to be the total left
-- derived functor of extension of scalars along `φ`.
/-- The point-level derived pullback is, by definition, the total left derived functor of
extension of scalars along the ring map `φ`. -/
theorem pointChangeOfRingsDerivedPullback_def (φ : B →+* B')
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived (ModuleCat.extendScalars φ))
      QisB] :
    pointChangeOfRingsDerivedPullback φ =
      Functor.totalLeftDerived
        (mapHomotopyCategoryToDerived (ModuleCat.extendScalars φ))
        DerivedCategory.Qh
        QisB := sorry

/-- The derived inverse-image functor on `D(\underline B)` attached to a ring map `B → B'`,
computed pointwise on `B`-module valued presheaves. -/
abbrev presheafChangeOfRingsDerivedPullback (φ : B →+* B')
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived
        ((Functor.whiskeringRight (Cᵒᵖ) (ModuleCat B) (ModuleCat B')).obj
          (ModuleCat.extendScalars φ)))
      QisBPresheaf] :
    DerivedCategory BPresheaf ⥤ DerivedCategory BPrimePresheaf :=
  Functor.totalLeftDerived
    (mapHomotopyCategoryToDerived
      ((Functor.whiskeringRight (Cᵒᵖ) (ModuleCat B) (ModuleCat B')).obj
        (ModuleCat.extendScalars φ)))
    DerivedCategory.Qh
    QisBPresheaf

-- Proof sketch: unfold `presheafChangeOfRingsDerivedPullback`; it is defined as the total left
-- derived functor of pointwise extension of scalars on `B`-module valued presheaves.
/-- The presheaf-level derived pullback is, by definition, the total left derived functor of the
pointwise extension-of-scalars functor on `B`-module valued presheaves. -/
theorem presheafChangeOfRingsDerivedPullback_def (φ : B →+* B')
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived
        ((Functor.whiskeringRight (Cᵒᵖ) (ModuleCat B) (ModuleCat B')).obj
          (ModuleCat.extendScalars φ)))
      QisBPresheaf] :
    presheafChangeOfRingsDerivedPullback φ =
      Functor.totalLeftDerived
        (mapHomotopyCategoryToDerived
          ((Functor.whiskeringRight (Cᵒᵖ) (ModuleCat B) (ModuleCat B')).obj
            (ModuleCat.extendScalars φ)))
        DerivedCategory.Qh
        QisBPresheaf := sorry

/-- The obvious right adjoint `D(B') ⥤ D(\underline B)` obtained by first restricting scalars
along `B → B'` and then taking the constant `B`-valued diagram on `Cᵒᵖ`. -/
abbrev categoryOverPointChangeOfRingsRightAdjoint (φ : B →+* B') :
    DerivedCategory (ModuleCat B') ⥤ DerivedCategory BPresheaf :=
  (ModuleCat.restrictScalars φ).mapDerivedCategory ⋙
    categoryOverPointDerivedInverseImage

-- Proof sketch: unfold `categoryOverPointChangeOfRingsRightAdjoint`; it is the composite of the
-- derived restriction-of-scalars functor with the derived constant-diagram functor.
/-- The obvious right adjoint factors as derived restriction of scalars followed by the derived
constant-diagram functor over `Cᵒᵖ`. -/
theorem categoryOverPointChangeOfRingsRightAdjoint_def (φ : B →+* B') :
    categoryOverPointChangeOfRingsRightAdjoint φ =
      (ModuleCat.restrictScalars φ).mapDerivedCategory ⋙
        (categoryOverPointDerivedInverseImage :
          DerivedCategory (ModuleCat B) ⥤ DerivedCategory BPresheaf) := sorry

-- Proof sketch: the two composites in the statement are assumed to be left adjoint to the same
-- explicit right adjoint `categoryOverPointChangeOfRingsRightAdjoint φ`. The uniqueness theorem
-- `Adjunction.leftAdjointUniq` then produces the canonical isomorphism between them.
/-- Lemma 21.39.6: in the category-over-a-point situation of Example 21.39.1, for a ring map
`φ : B →+* B'`, the composite obtained by first changing rings on `B`-module valued presheaves
and then applying `L\pi'_!` is canonically isomorphic to the composite obtained by first applying
`L\pi_!` and then changing rings on the point. This is the library-facing form of the textbook
base-change identity between `L\pi_!`, `Lh^*`, `Lf^*`, and `L\pi'_!`. -/
abbrev categoryOverPoint_derivedLowerShriek_changeOfRingsIso (φ : B →+* B')
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived (ModuleCat.extendScalars φ))
      QisB]
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived
        ((Functor.whiskeringRight (Cᵒᵖ) (ModuleCat B) (ModuleCat B')).obj
          (ModuleCat.extendScalars φ)))
      QisBPresheaf]
    [Functor.HasLeftDerivedFunctor
      categoryOverPointLowerShriekToDerived
      QisBPresheaf]
    [Functor.HasLeftDerivedFunctor
      categoryOverPointLowerShriekToDerived
      QisBPrimePresheaf]
    (adj_presheaf :
      presheafChangeOfRingsDerivedPullback φ ⋙
          (categoryOverPointDerivedLowerShriek :
            DerivedCategory BPrimePresheaf ⥤ DerivedCategory (ModuleCat B')) ⊣
        categoryOverPointChangeOfRingsRightAdjoint φ)
    (adj_point :
      (categoryOverPointDerivedLowerShriek :
          DerivedCategory BPresheaf ⥤ DerivedCategory (ModuleCat B)) ⋙
          pointChangeOfRingsDerivedPullback φ ⊣
        categoryOverPointChangeOfRingsRightAdjoint φ) :
    presheafChangeOfRingsDerivedPullback φ ⋙
        (categoryOverPointDerivedLowerShriek :
          DerivedCategory BPrimePresheaf ⥤ DerivedCategory (ModuleCat B')) ≅
      (categoryOverPointDerivedLowerShriek :
          DerivedCategory BPresheaf ⥤ DerivedCategory (ModuleCat B)) ⋙
        pointChangeOfRingsDerivedPullback φ :=
  Adjunction.leftAdjointUniq adj_presheaf adj_point

-- Proof sketch: unfold `categoryOverPoint_derivedLowerShriek_changeOfRingsIso`; it is defined to
-- be the uniqueness isomorphism between the two specified left adjoints of the same right adjoint.
/-- The base-change isomorphism is defined by uniqueness of left adjoints to the obvious derived
restriction-constant functor. -/
theorem categoryOverPoint_derivedLowerShriek_changeOfRingsIso_def (φ : B →+* B')
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived (ModuleCat.extendScalars φ))
      QisB]
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived
        ((Functor.whiskeringRight (Cᵒᵖ) (ModuleCat B) (ModuleCat B')).obj
          (ModuleCat.extendScalars φ)))
      QisBPresheaf]
    [Functor.HasLeftDerivedFunctor
      categoryOverPointLowerShriekToDerived
      QisBPresheaf]
    [Functor.HasLeftDerivedFunctor
      categoryOverPointLowerShriekToDerived
      QisBPrimePresheaf]
    (adj_presheaf :
      presheafChangeOfRingsDerivedPullback φ ⋙
          (categoryOverPointDerivedLowerShriek :
            DerivedCategory BPrimePresheaf ⥤ DerivedCategory (ModuleCat B')) ⊣
        categoryOverPointChangeOfRingsRightAdjoint φ)
    (adj_point :
      (categoryOverPointDerivedLowerShriek :
          DerivedCategory BPresheaf ⥤ DerivedCategory (ModuleCat B)) ⋙
          pointChangeOfRingsDerivedPullback φ ⊣
        categoryOverPointChangeOfRingsRightAdjoint φ) :
    categoryOverPoint_derivedLowerShriek_changeOfRingsIso φ
        adj_presheaf adj_point =
      Adjunction.leftAdjointUniq adj_presheaf adj_point := sorry

end

end CategoryTheory

/-! ### Lemma_21_39_7 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open Opposite
open scoped Simplicial

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory

section Generic

variable {C : Type u} [Category.{v} C]

/-- Two simplicial objects are homotopy equivalent if there are maps in both directions whose
composites are simplicially homotopic to the corresponding identity morphisms. -/
def SimplicialHomotopyEquivalent (X Y : SimplicialObject C) : Prop :=
  ∃ (f : X ⟶ Y) (g : Y ⟶ X),
    Nonempty (SimplicialObject.Homotopy (f ≫ g) (𝟙 X)) ∧
      Nonempty (SimplicialObject.Homotopy (g ≫ f) (𝟙 Y))

/-- The simplicial object of `Cᵒᵖ` corresponding to a cosimplicial object of `C`. -/
private abbrev oppositeSimplicialObject (Ubullet : CosimplicialObject C) :
    SimplicialObject Cᵒᵖ :=
  (CategoryTheory.cosimplicialSimplicialEquiv C).functor.obj (op Ubullet)

/-- The simplicial set `n ↦ \operatorname{Mor}_{\mathcal C}(U_n, U)` attached to a cosimplicial
object `U_•` and an object `U` of `C`. -/
private abbrev cosimplicialHomSSet (Ubullet : CosimplicialObject C) (U : C) :
    SSet.{v} :=
  ((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ (Type v)).obj
      (oppositeSimplicialObject Ubullet)).obj
    (yoneda.obj U)

end Generic

section AddCommGrp

variable {C : Type u} [Category.{v} C]
variable [HasColimitsOfShape Cᵒᵖ AddCommGrpCat]

/-- The lower shriek functor for the projection from a category over a point on abelian
presheaves is the colimit functor. -/
private abbrev abelianCategoryOverPointLowerShriek :
    (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ AddCommGrpCat :=
  colim

/-- The homotopy-to-derived functor whose total left derived functor is the derived lower shriek on
abelian presheaves over a point. -/
private abbrev abelianCategoryOverPointLowerShriekToDerived :
    HomotopyCategory (Cᵒᵖ ⥤ AddCommGrpCat) (ComplexShape.up ℤ) ⥤
      DerivedCategory AddCommGrpCat :=
  abelianCategoryOverPointLowerShriek.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    (DerivedCategory.Qh :
      HomotopyCategory AddCommGrpCat (ComplexShape.up ℤ) ⥤ DerivedCategory AddCommGrpCat)

/-- The derived lower shriek functor `L\pi_!` for abelian presheaves on a category over a point.
-/
private abbrev abelianCategoryOverPointDerivedLowerShriek
    [Functor.HasLeftDerivedFunctor
      (abelianCategoryOverPointLowerShriekToDerived :
        HomotopyCategory (Cᵒᵖ ⥤ AddCommGrpCat) (ComplexShape.up ℤ) ⥤
          DerivedCategory AddCommGrpCat)
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ AddCommGrpCat) (ComplexShape.up ℤ))] :
    DerivedCategory (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ DerivedCategory AddCommGrpCat :=
  Functor.totalLeftDerived
    (abelianCategoryOverPointLowerShriekToDerived :
      HomotopyCategory (Cᵒᵖ ⥤ AddCommGrpCat) (ComplexShape.up ℤ) ⥤
        DerivedCategory AddCommGrpCat)
    (DerivedCategory.Qh :
      HomotopyCategory (Cᵒᵖ ⥤ AddCommGrpCat) (ComplexShape.up ℤ) ⥤
        DerivedCategory (Cᵒᵖ ⥤ AddCommGrpCat))
    (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ AddCommGrpCat) (ComplexShape.up ℤ))

/-- Evaluating an abelian presheaf on the simplicial object attached to `U_•` produces a
simplicial abelian group. -/
private abbrev abelianPresheafEvaluationSimplicialObject (Ubullet : CosimplicialObject C) :
    (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ SimplicialObject AddCommGrpCat :=
  (Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ AddCommGrpCat).obj
    (oppositeSimplicialObject Ubullet)

/-- The chain complex associated to the simplicial abelian group `\mathcal F(U_•)`. -/
private abbrev abelianPresheafEvaluationChainComplex (Ubullet : CosimplicialObject C) :
    (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ ChainComplex AddCommGrpCat ℕ :=
  abelianPresheafEvaluationSimplicialObject Ubullet ⋙ alternatingFaceMapComplex AddCommGrpCat

/-- The derived-category realization of the simplicial abelian group `\mathcal F(U_•)`. -/
noncomputable abbrev abelianCosimplicialEvaluationToDerived (Ubullet : CosimplicialObject C) :
    (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ DerivedCategory AddCommGrpCat :=
  abelianPresheafEvaluationChainComplex Ubullet ⋙
    (ComplexShape.embeddingDownNat.extendFunctor AddCommGrpCat) ⋙
    DerivedCategory.Q

variable [Functor.HasLeftDerivedFunctor
  (abelianCategoryOverPointLowerShriekToDerived :
    HomotopyCategory (Cᵒᵖ ⥤ AddCommGrpCat) (ComplexShape.up ℤ) ⥤
      DerivedCategory AddCommGrpCat)
  (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ AddCommGrpCat) (ComplexShape.up ℤ))]

-- Proof sketch: resolve each abelian presheaf by sums of representables, evaluate the resolution
-- on `U_•`, and use the assumption that every simplicial set `Mor_C(U_•, U)` is homotopy
-- equivalent to `Δ[0]` to identify the resulting simplicial abelian groups with the corresponding
-- representable resolutions of the colimit. This yields a functorial isomorphism in the derived
-- category.
/-- Lemma 21.39.7 (1): in the category-over-a-point situation of Example 21.39.1, if every
simplicial set `\operatorname{Mor}_{\mathcal C}(U_\bullet, U)` is homotopy equivalent to the
singleton simplicial set `\Delta[0]`, then the derived lower shriek of a degree-zero abelian
presheaf is functorially isomorphic to the derived object represented by the simplicial abelian
group `\mathcal F(U_\bullet)`. -/
theorem categoryOverPointDerivedLowerShriek_singleFunctor_isIsomorphic_abelianCosimplicialEvaluation
    (Ubullet : CosimplicialObject C)
    (hUbullet : ∀ U : C,
      SimplicialHomotopyEquivalent
        (cosimplicialHomSSet Ubullet U)
        (Δ[0] : SSet)) :
    IsIsomorphic
      (((DerivedCategory.singleFunctor (Cᵒᵖ ⥤ AddCommGrpCat) (0 : ℤ)) ⋙
          abelianCategoryOverPointDerivedLowerShriek :
            (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ DerivedCategory AddCommGrpCat))
      (abelianCosimplicialEvaluationToDerived Ubullet) := sorry

end AddCommGrp

section Module

variable {C : Type u} [Category.{v} C]
variable (B : Type w) [Ring B]
variable [HasColimitsOfShape Cᵒᵖ (ModuleCat B)]

/-- The lower shriek functor for the projection from a category over a point on presheaves of
`B`-modules is the colimit functor. -/
private abbrev moduleCategoryOverPointLowerShriek :
    (Cᵒᵖ ⥤ ModuleCat B) ⥤ ModuleCat B :=
  colim

/-- The homotopy-to-derived functor whose total left derived functor is the derived lower shriek on
presheaves of `B`-modules over a point. -/
private abbrev moduleCategoryOverPointLowerShriekToDerived :
    HomotopyCategory (Cᵒᵖ ⥤ ModuleCat B) (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat B) :=
  (moduleCategoryOverPointLowerShriek B).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat B) (ComplexShape.up ℤ) ⥤ DerivedCategory (ModuleCat B))

/-- The derived lower shriek functor `L\pi_!` for presheaves of `B`-modules on a category over a
point. -/
private abbrev moduleCategoryOverPointDerivedLowerShriek
    [Functor.HasLeftDerivedFunctor
      (moduleCategoryOverPointLowerShriekToDerived B :
        HomotopyCategory (Cᵒᵖ ⥤ ModuleCat B) (ComplexShape.up ℤ) ⥤
          DerivedCategory (ModuleCat B))
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ ModuleCat B) (ComplexShape.up ℤ))] :
    DerivedCategory (Cᵒᵖ ⥤ ModuleCat B) ⥤ DerivedCategory (ModuleCat B) :=
  Functor.totalLeftDerived
    (moduleCategoryOverPointLowerShriekToDerived B :
      HomotopyCategory (Cᵒᵖ ⥤ ModuleCat B) (ComplexShape.up ℤ) ⥤
        DerivedCategory (ModuleCat B))
    (DerivedCategory.Qh :
      HomotopyCategory (Cᵒᵖ ⥤ ModuleCat B) (ComplexShape.up ℤ) ⥤
        DerivedCategory (Cᵒᵖ ⥤ ModuleCat B))
    (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ ModuleCat B) (ComplexShape.up ℤ))

/-- Evaluating a presheaf of `B`-modules on the simplicial object attached to `U_•` produces a
simplicial object of `B`-modules. -/
private abbrev modulePresheafEvaluationSimplicialObject (Ubullet : CosimplicialObject C) :
    (Cᵒᵖ ⥤ ModuleCat B) ⥤ SimplicialObject (ModuleCat B) :=
  (Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ (ModuleCat B)).obj
    (oppositeSimplicialObject Ubullet)

/-- The chain complex associated to the simplicial `B`-module object `\mathcal F(U_•)`. -/
private abbrev modulePresheafEvaluationChainComplex (Ubullet : CosimplicialObject C) :
    (Cᵒᵖ ⥤ ModuleCat B) ⥤ ChainComplex (ModuleCat B) ℕ :=
  modulePresheafEvaluationSimplicialObject B Ubullet ⋙
    alternatingFaceMapComplex (ModuleCat B)

/-- The derived-category realization of the simplicial `B`-module object `\mathcal F(U_•)`. -/
noncomputable abbrev moduleCosimplicialEvaluationToDerived (Ubullet : CosimplicialObject C) :
    (Cᵒᵖ ⥤ ModuleCat B) ⥤ DerivedCategory (ModuleCat B) :=
  modulePresheafEvaluationChainComplex B Ubullet ⋙
    (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat B)) ⋙
    DerivedCategory.Q

variable [Functor.HasLeftDerivedFunctor
  (moduleCategoryOverPointLowerShriekToDerived B :
    HomotopyCategory (Cᵒᵖ ⥤ ModuleCat B) (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat B))
  (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ ModuleCat B) (ComplexShape.up ℤ))]

-- Proof sketch: apply the abelian-sheaf argument objectwise to the underlying additive presheaf of
-- a `B`-module presheaf, use the compatibility of `L\pi_!` for modules with the abelian version,
-- and transport the resulting functorial comparison back to `D(B)`.
/-- Lemma 21.39.7 (2): under the same hypothesis on `U_\bullet`, the derived lower shriek of a
degree-zero presheaf of `B`-modules is functorially isomorphic to the derived object represented
by the simplicial `B`-module object `\mathcal F(U_\bullet)`. -/
theorem categoryOverPointDerivedLowerShriek_singleFunctor_isIsomorphic_moduleCosimplicialEvaluation
    (Ubullet : CosimplicialObject C)
    (hUbullet : ∀ U : C,
      SimplicialHomotopyEquivalent
        (cosimplicialHomSSet Ubullet U)
        (Δ[0] : SSet)) :
    IsIsomorphic
      (((DerivedCategory.singleFunctor (Cᵒᵖ ⥤ ModuleCat B) (0 : ℤ)) ⋙
          moduleCategoryOverPointDerivedLowerShriek B :
            (Cᵒᵖ ⥤ ModuleCat B) ⥤ DerivedCategory (ModuleCat B)))
      (moduleCosimplicialEvaluationToDerived B Ubullet) := sorry

end Module

end CategoryTheory

/-! ### Lemma_21_39_8 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite
open scoped Simplicial

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory

section Generic

variable {C : Type u} [Category.{v} C]
variable {C' : Type u} [Category.{v} C']
variable {A : Type w} [Category A] [Abelian A] [HasDerivedCategory A]
variable [HasDerivedCategory (Cᵒᵖ ⥤ A)]
variable [HasColimitsOfShape Cᵒᵖ A]

/-- Two simplicial objects are homotopy equivalent if there are maps in both directions whose
composites are simplicially homotopic to the corresponding identity morphisms. -/
def SimplicialObjectHomotopyEquivalent (X Y : SimplicialObject C) : Prop :=
  ∃ (f : X ⟶ Y) (g : Y ⟶ X),
    Nonempty (SimplicialObject.Homotopy (f ≫ g) (𝟙 X)) ∧
      Nonempty (SimplicialObject.Homotopy (g ≫ f) (𝟙 Y))

/-- The simplicial set `n ↦ \operatorname{Mor}_{\mathcal C}(U_n, U)` attached to a cosimplicial
object `U_•` and an object `U` of `C`. -/
private abbrev cosimplicialHomSSet (Ubullet : CosimplicialObject C) (U : C) :
    SSet.{v} :=
  ((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ (Type v)).obj
      ((CategoryTheory.cosimplicialSimplicialEquiv C).functor.obj (op Ubullet))).obj
    (yoneda.obj U)

/-- Applying a functor to a cosimplicial object degreewise. -/
private abbrev whiskeredCosimplicialObject (u : C' ⥤ C) (Ubullet : CosimplicialObject C') :
    CosimplicialObject C :=
  ((CosimplicialObject.whiskering C' C).obj u).obj Ubullet

/-- Every simplicial set of maps from `U_•` to an object of `C` is homotopy equivalent to the
singleton simplicial set `Δ[0]`. This is the hypothesis appearing in Lemma `21.39.7`. -/
def CosimplicialObjectHasPointlikeHomSpaces (Ubullet : CosimplicialObject C) : Prop :=
  ∀ U : C,
    SimplicialObjectHomotopyEquivalent
      (cosimplicialHomSSet Ubullet U)
      (Δ[0] : SSet)

/-- The homotopy-to-derived functor whose total left derived functor is the derived lower shriek
for the projection from a category over a point. -/
abbrev categoryOverPointColimitToDerived :
    HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤ DerivedCategory A :=
  ((colim : (Cᵒᵖ ⥤ A) ⥤ A)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- The derived lower shriek functor `L\pi_!` for the projection from a category over a point. -/
abbrev categoryOverPointDerivedColimit
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived :
        HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤ DerivedCategory A)
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ))] :
    DerivedCategory (Cᵒᵖ ⥤ A) ⥤ DerivedCategory A :=
  Functor.totalLeftDerived
    (categoryOverPointColimitToDerived :
      HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤ DerivedCategory A)
    (DerivedCategory.Qh :
      HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤
        DerivedCategory (Cᵒᵖ ⥤ A))
    (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ))

end Generic

section AddCommGrp

variable {C : Type u} [Category.{v} C]
variable {C' : Type u} [Category.{v} C']
variable (u : C' ⥤ C)

local notation "AbPresheaf" => Cᵒᵖ ⥤ AddCommGrpCat
local notation "AbPresheaf'" => C'ᵒᵖ ⥤ AddCommGrpCat
local notation "QisAbPresheaf" => HomotopyCategory.quasiIso AbPresheaf (up ℤ)
local notation "QisAbPresheaf'" => HomotopyCategory.quasiIso AbPresheaf' (up ℤ)
local notation "AbelianColimitToDerived" =>
  (categoryOverPointColimitToDerived :
    HomotopyCategory AbPresheaf (up ℤ) ⥤ DerivedCategory AddCommGrpCat)
local notation "AbelianColimitToDerived'" =>
  (categoryOverPointColimitToDerived :
    HomotopyCategory AbPresheaf' (up ℤ) ⥤ DerivedCategory AddCommGrpCat)

/-- The exact inverse-image functor on derived categories induced by precomposition with
`u.op` on abelian presheaves. -/
private abbrev abelianPrecompositionDerivedInverseImage :
    DerivedCategory AbPresheaf ⥤ DerivedCategory AbPresheaf' :=
  ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ AddCommGrpCat).obj u.op).mapDerivedCategory

-- Proof sketch: choose `U'_•` from the hypothesis. Lemma `21.39.7` applied in `C'` identifies
-- `Lπ'_!` with evaluation on `U'_•`, and applied in `C` to the whiskered cosimplicial object
-- `u(U'_•)` identifies `Lπ_!` with evaluation on `u(U'_•)`. Since `g⁻¹` is precomposition with
-- `u`, these two evaluation functors agree, yielding the desired functor isomorphism.
/-- Lemma 21.39.8 (1): if there is a cosimplicial object `U'_•` of `\mathcal C'` to which Lemma
21.39.7 applies both in `\mathcal C'` and, after applying `u`, in `\mathcal C`, then the derived
lower shriek from `\mathcal C'` to a point composed with inverse image along `u` is functorially
isomorphic to the derived lower shriek from `\mathcal C` to a point on
`D(\mathcal C, \mathrm{Ab}) \to D(\mathrm{Ab})`. -/
theorem abelianPrecompositionDerivedInverseImage_comp_categoryOverPointDerivedLowerShriek_isomorphic
    [HasColimitsOfShape Cᵒᵖ AddCommGrpCat]
    [HasColimitsOfShape C'ᵒᵖ AddCommGrpCat]
    [Functor.HasLeftDerivedFunctor AbelianColimitToDerived QisAbPresheaf]
    [Functor.HasLeftDerivedFunctor AbelianColimitToDerived' QisAbPresheaf']
    (hUbullet :
      ∃ Ubullet' : CosimplicialObject C',
        CosimplicialObjectHasPointlikeHomSpaces Ubullet' ∧
          CosimplicialObjectHasPointlikeHomSpaces
            (whiskeredCosimplicialObject u Ubullet')) :
    IsIsomorphic
      ((abelianPrecompositionDerivedInverseImage u) ⋙
        (categoryOverPointDerivedColimit :
          DerivedCategory AbPresheaf' ⥤ DerivedCategory AddCommGrpCat))
      (categoryOverPointDerivedColimit :
        DerivedCategory AbPresheaf ⥤ DerivedCategory AddCommGrpCat) := sorry

end AddCommGrp

section Module

variable {C : Type u} [Category.{v} C]
variable {C' : Type u} [Category.{v} C']
variable (B : Type w) [Ring B]
variable (u : C' ⥤ C)

local notation "BPresheaf" => Cᵒᵖ ⥤ ModuleCat B
local notation "BPresheaf'" => C'ᵒᵖ ⥤ ModuleCat B
local notation "QisBPresheaf" => HomotopyCategory.quasiIso BPresheaf (up ℤ)
local notation "QisBPresheaf'" => HomotopyCategory.quasiIso BPresheaf' (up ℤ)
local notation "ModuleColimitToDerived" =>
  (categoryOverPointColimitToDerived :
    HomotopyCategory BPresheaf (up ℤ) ⥤ DerivedCategory (ModuleCat B))
local notation "ModuleColimitToDerived'" =>
  (categoryOverPointColimitToDerived :
    HomotopyCategory BPresheaf' (up ℤ) ⥤ DerivedCategory (ModuleCat B))

/-- The exact inverse-image functor on derived categories induced by precomposition with
`u.op` on presheaves of `B`-modules. -/
private abbrev modulePrecompositionDerivedInverseImage :
    DerivedCategory BPresheaf ⥤ DerivedCategory BPresheaf' :=
  ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ (ModuleCat B)).obj u.op).mapDerivedCategory

-- Proof sketch: choose `U'_•` from the hypothesis. Lemma `21.39.7` applied in `C'` identifies
-- `Lπ'_!` with evaluation on `U'_•`, and applied in `C` to the whiskered cosimplicial object
-- `u(U'_•)` identifies `Lπ_!` with evaluation on `u(U'_•)`. Since `g⁻¹` is precomposition with
-- `u`, the two evaluation functors coincide, giving the module-valued comparison isomorphism.
/-- Lemma 21.39.8 (2): under the same cosimplicial-object hypothesis, the derived lower shriek
from `\mathcal C'` to a point composed with inverse image along `u` is functorially isomorphic
to the derived lower shriek from `\mathcal C` to a point on
`D(\mathcal C, \underline{B}) \to D(B)`. -/
theorem modulePrecompositionDerivedInverseImage_comp_categoryOverPointDerivedLowerShriek_isomorphic
    [HasColimitsOfShape Cᵒᵖ (ModuleCat B)]
    [HasColimitsOfShape C'ᵒᵖ (ModuleCat B)]
    [Functor.HasLeftDerivedFunctor ModuleColimitToDerived QisBPresheaf]
    [Functor.HasLeftDerivedFunctor ModuleColimitToDerived' QisBPresheaf']
    (hUbullet :
      ∃ Ubullet' : CosimplicialObject C',
        CosimplicialObjectHasPointlikeHomSpaces Ubullet' ∧
          CosimplicialObjectHasPointlikeHomSpaces
            (whiskeredCosimplicialObject u Ubullet')) :
    IsIsomorphic
      ((modulePrecompositionDerivedInverseImage B u) ⋙
        (categoryOverPointDerivedColimit :
          DerivedCategory BPresheaf' ⥤ DerivedCategory (ModuleCat B)))
      (categoryOverPointDerivedColimit :
        DerivedCategory BPresheaf ⥤ DerivedCategory (ModuleCat B)) := sorry

end Module

end CategoryTheory

/-! ### Lemma_21_39_9 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u₁ v₁ u₂ v₂ w

namespace CategoryTheory

section

variable {C₁ : Type u₁} [Category.{v₁} C₁]
variable {C₂ : Type u₂} [Category.{v₂} C₂]
variable {B : Type w} [CommRing B]

local notation "BPresheaf₁" => C₁ᵒᵖ ⥤ ModuleCat B
local notation "BPresheaf₂" => C₂ᵒᵖ ⥤ ModuleCat B
local notation "ProductBPresheaf" => (C₁ × C₂)ᵒᵖ ⥤ ModuleCat B
local notation "Qis₁" => HomotopyCategory.quasiIso BPresheaf₁ (up ℤ)
local notation "Qis₂" => HomotopyCategory.quasiIso BPresheaf₂ (up ℤ)
local notation "QisProduct" => HomotopyCategory.quasiIso ProductBPresheaf (up ℤ)

/-- The homotopy-to-derived functor obtained by taking colimits of `B`-module valued presheaf
complexes on `C₁`. -/
private abbrev firstColimitToDerived [HasColimitsOfShape C₁ᵒᵖ (ModuleCat B)] :
    HomotopyCategory BPresheaf₁ (up ℤ) ⥤ DerivedCategory (ModuleCat B) :=
  (colim : BPresheaf₁ ⥤ ModuleCat B).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The homotopy-to-derived functor obtained by taking colimits of `B`-module valued presheaf
complexes on `C₂`. -/
private abbrev secondColimitToDerived [HasColimitsOfShape C₂ᵒᵖ (ModuleCat B)] :
    HomotopyCategory BPresheaf₂ (up ℤ) ⥤ DerivedCategory (ModuleCat B) :=
  (colim : BPresheaf₂ ⥤ ModuleCat B).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The homotopy-to-derived functor obtained by taking colimits of `B`-module valued presheaf
complexes on the product category `C₁ × C₂`. -/
private abbrev productColimitToDerived [HasColimitsOfShape (C₁ × C₂)ᵒᵖ (ModuleCat B)] :
    HomotopyCategory ProductBPresheaf (up ℤ) ⥤ DerivedCategory (ModuleCat B) :=
  (colim : ProductBPresheaf ⥤ ModuleCat B).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The exact inverse-image functor on derived categories induced by precomposition with the first
projection `C₁ × C₂ ⥤ C₁`. -/
private abbrev productLeftProjectionDerivedInverseImage :
    DerivedCategory BPresheaf₁ ⥤ DerivedCategory ProductBPresheaf :=
  ((Functor.whiskeringLeft (C₁ × C₂)ᵒᵖ C₁ᵒᵖ (ModuleCat B)).obj
      (CategoryTheory.Prod.fst C₁ C₂).op).mapDerivedCategory

/-- The exact inverse-image functor on derived categories induced by precomposition with the
second projection `C₁ × C₂ ⥤ C₂`. -/
private abbrev productRightProjectionDerivedInverseImage :
    DerivedCategory BPresheaf₂ ⥤ DerivedCategory ProductBPresheaf :=
  ((Functor.whiskeringLeft (C₁ × C₂)ᵒᵖ C₂ᵒᵖ (ModuleCat B)).obj
      (CategoryTheory.Prod.snd C₁ C₂).op).mapDerivedCategory

/-- The derived lower shriek `L\pi_{1,!}` from `B`-module valued presheaves on `C₁` to
`D(B)`. -/
private abbrev firstDerivedLowerShriek
    [HasColimitsOfShape C₁ᵒᵖ (ModuleCat B)]
    [Functor.HasLeftDerivedFunctor firstColimitToDerived Qis₁] :
    DerivedCategory BPresheaf₁ ⥤ DerivedCategory (ModuleCat B) :=
  Functor.totalLeftDerived firstColimitToDerived
    (DerivedCategory.Qh : HomotopyCategory BPresheaf₁ (up ℤ) ⥤ DerivedCategory BPresheaf₁)
    Qis₁

/-- The derived lower shriek `L\pi_{2,!}` from `B`-module valued presheaves on `C₂` to
`D(B)`. -/
private abbrev secondDerivedLowerShriek
    [HasColimitsOfShape C₂ᵒᵖ (ModuleCat B)]
    [Functor.HasLeftDerivedFunctor secondColimitToDerived Qis₂] :
    DerivedCategory BPresheaf₂ ⥤ DerivedCategory (ModuleCat B) :=
  Functor.totalLeftDerived secondColimitToDerived
    (DerivedCategory.Qh : HomotopyCategory BPresheaf₂ (up ℤ) ⥤ DerivedCategory BPresheaf₂)
    Qis₂

/-- The derived lower shriek `L(\pi₁ × \pi₂)_!` from `B`-module valued presheaves on
`C₁ × C₂` to `D(B)`. -/
private abbrev productDerivedLowerShriek
    [HasColimitsOfShape (C₁ × C₂)ᵒᵖ (ModuleCat B)]
    [Functor.HasLeftDerivedFunctor productColimitToDerived QisProduct] :
    DerivedCategory ProductBPresheaf ⥤ DerivedCategory (ModuleCat B) :=
  Functor.totalLeftDerived productColimitToDerived
    (DerivedCategory.Qh :
      HomotopyCategory ProductBPresheaf (up ℤ) ⥤ DerivedCategory ProductBPresheaf)
    QisProduct

-- Proof sketch: resolve both inputs by projective complexes built from the generators
-- `j_{U!}\underline B_U` and `j_{V!}\underline B_V`, use Example `21.39.3` to identify the exact
-- inverse images along the two projection functors, and compute both derived colimits using
-- Lemma `21.37.2`. On the generators both sides evaluate to `B`, and functoriality plus passage
-- to derived colimits yields the comparison isomorphism.
/-- Lemma 21.39.9: for the projection functors `uᵢ : \mathcal C₁ × \mathcal C₂ \to \mathcal Cᵢ`,
the derived lower shriek from the product category to a point sends the tensor product of the two
inverse images `g₁^{-1} K₁` and `g₂^{-1} K₂` to the tensor product of the derived lower shrieks
`L\pi_{1,!}(K₁)` and `L\pi_{2,!}(K₂)` in `D(B)`. This is the product-site, module-valued
presheaf formalization of the Stacks identity
`L(\pi₁ × \pi₂)_!(g₁^{-1} K₁ \otimes_{\underline B}^{\mathbf L} g₂^{-1} K₂)
  = L\pi_{1,!}(K₁) \otimes_B^{\mathbf L} L\pi_{2,!}(K₂)`. -/
theorem product_derivedLowerShriek_tensor_projectionInverseImages_isomorphic
    [HasColimitsOfShape C₁ᵒᵖ (ModuleCat B)]
    [HasColimitsOfShape C₂ᵒᵖ (ModuleCat B)]
    [HasColimitsOfShape (C₁ × C₂)ᵒᵖ (ModuleCat B)]
    [Functor.HasLeftDerivedFunctor firstColimitToDerived Qis₁]
    [Functor.HasLeftDerivedFunctor secondColimitToDerived Qis₂]
    [Functor.HasLeftDerivedFunctor productColimitToDerived QisProduct]
    [MonoidalCategory (DerivedCategory BPresheaf₁)]
    [MonoidalCategory (DerivedCategory BPresheaf₂)]
    [MonoidalCategory (DerivedCategory ProductBPresheaf)]
    [MonoidalCategory (DerivedCategory (ModuleCat B))]
    (K₁ : DerivedCategory BPresheaf₁) (K₂ : DerivedCategory BPresheaf₂) :
    IsIsomorphic
      ((productDerivedLowerShriek).obj
        (((productLeftProjectionDerivedInverseImage).obj K₁) ⊗
          ((productRightProjectionDerivedInverseImage).obj K₂)))
      (((firstDerivedLowerShriek).obj K₁) ⊗ ((secondDerivedLowerShriek).obj K₂)) := sorry

end

end CategoryTheory

/-! ### Lemma_21_39_10 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open Opposite
open scoped Simplicial

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {B : Type w} [CommRing B]

local notation "BPresheaf" => Cᵒᵖ ⥤ ModuleCat B
local notation "QisBPresheaf" => HomotopyCategory.quasiIso BPresheaf (up ℤ)

/-- Two simplicial objects are homotopy equivalent if there are maps in both directions whose
composites are simplicially homotopic to the corresponding identity morphisms. -/
def SimplicialObjectHomotopyEquivalent (X Y : SimplicialObject C) : Prop :=
  ∃ (f : X ⟶ Y) (g : Y ⟶ X),
    Nonempty (SimplicialObject.Homotopy (f ≫ g) (𝟙 X)) ∧
      Nonempty (SimplicialObject.Homotopy (g ≫ f) (𝟙 Y))

/-- The simplicial set `n ↦ \operatorname{Mor}_{\mathcal C}(U_n, U)` attached to a cosimplicial
object `U_•` and an object `U` of `C`. -/
private abbrev cosimplicialHomSSet (Ubullet : CosimplicialObject C) (U : C) :
    SSet.{v} :=
  ((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ (Type v)).obj
      ((CategoryTheory.cosimplicialSimplicialEquiv C).functor.obj (op Ubullet))).obj
    (yoneda.obj U)

/-- Every simplicial set of maps from `U_•` to an object of `C` is homotopy equivalent to the
singleton simplicial set `Δ[0]`. This is the hypothesis appearing in Lemma `21.39.7`. -/
def CosimplicialObjectHasPointlikeHomSpaces (Ubullet : CosimplicialObject C) : Prop :=
  ∀ U : C,
    SimplicialObjectHomotopyEquivalent
      (cosimplicialHomSSet Ubullet U)
      (Δ[0] : SSet)

/-- The homotopy-to-derived functor whose total left derived functor is the derived lower shriek
for the projection from a category over a point. -/
abbrev categoryOverPointColimitToDerived :
    HomotopyCategory BPresheaf (up ℤ) ⥤ DerivedCategory (ModuleCat B) :=
  ((colim : BPresheaf ⥤ ModuleCat B)).mapHomotopyCategory (up ℤ) ⋙
    DerivedCategory.Qh

/-- The derived lower shriek functor `L\pi_!` for presheaves of `B`-modules on a category over a
point. -/
abbrev categoryOverPointDerivedColimit
    [HasColimitsOfShape Cᵒᵖ (ModuleCat B)]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived :
        HomotopyCategory BPresheaf (up ℤ) ⥤ DerivedCategory (ModuleCat B))
      QisBPresheaf] :
    DerivedCategory BPresheaf ⥤ DerivedCategory (ModuleCat B) :=
  Functor.totalLeftDerived
    (categoryOverPointColimitToDerived :
      HomotopyCategory BPresheaf (up ℤ) ⥤ DerivedCategory (ModuleCat B))
    (DerivedCategory.Qh :
      HomotopyCategory BPresheaf (up ℤ) ⥤ DerivedCategory BPresheaf)
    QisBPresheaf

-- Proof sketch: choose a cosimplicial object `U_•` with pointlike hom-spaces. Apply Lemma
-- `21.39.8` to the diagonal functor `\mathcal C → \mathcal C × \mathcal C` and use the product
-- description of the simplicial mapping sets together with Simplicial, Lemma `14.26.10` to see
-- that the hypothesis needed there is satisfied. Then identify the tensor product on
-- `D(\underline B)` with the inverse image along the diagonal of the tensor of the two projection
-- inverse images by Lemma `21.18.4`, and finish with Lemma `21.39.9`.
/-- Lemma 21.39.10: if there exists a cosimplicial object `U_\bullet` of `\mathcal C` to which
Lemma `21.39.7` applies, then the derived lower shriek for the category-over-a-point situation
commutes with the derived tensor product on `D(\underline B)`. In Lean this is expressed as an
objectwise isomorphism
`L\pi_!(K₁ \otimes_{\underline B}^{\mathbf L} K₂) \cong
  L\pi_!(K₁) \otimes_B^{\mathbf L} L\pi_!(K₂)`. -/
theorem categoryOverPointDerivedLowerShriek_tensor_isomorphic
    [HasColimitsOfShape Cᵒᵖ (ModuleCat B)]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived :
        HomotopyCategory BPresheaf (up ℤ) ⥤ DerivedCategory (ModuleCat B))
      QisBPresheaf]
    [MonoidalCategory (DerivedCategory BPresheaf)]
    [MonoidalCategory (DerivedCategory (ModuleCat B))]
    (hUbullet : ∃ Ubullet : CosimplicialObject C,
      CosimplicialObjectHasPointlikeHomSpaces Ubullet)
    (K₁ K₂ : DerivedCategory BPresheaf) :
    IsIsomorphic
      ((categoryOverPointDerivedColimit).obj (K₁ ⊗ K₂))
      (((categoryOverPointDerivedColimit).obj K₁) ⊗
        ((categoryOverPointDerivedColimit).obj K₂)) := sorry

end

end CategoryTheory

/-! ### Remark_21_39_11_Simplicial_modules (from Chap21) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicTopology
open Opposite
open scoped Simplicial

noncomputable section

universe u

namespace CategoryTheory

/-- The associated chain complex `s(M_•)` of a simplicial `B`-module `M_•`, given by the
alternating face map construction. -/
abbrev simplicialModuleAssociatedComplex (B : Type u) [CommRing B]
    (M : SimplicialObject (ModuleCat B)) : ChainComplex (ModuleCat B) ℕ :=
  (alternatingFaceMapComplex (ModuleCat B)).obj M

/-- A simplicial `B`-module is termwise flat if each module of simplices is flat over `B`. -/
abbrev simplicialModuleTermwiseFlat (B : Type u) [CommRing B]
    (M : SimplicialObject (ModuleCat B)) : Prop :=
  ∀ n : ℕ, Module.Flat B (M _⦋n⦌)

-- Proof sketch: unfold `simplicialModuleAssociatedComplex`; it is defined to be the alternating
-- face map complex attached to the simplicial module.
/-- The notation `s(M_•)` is implemented by the alternating face map complex of `M_•`. -/
theorem simplicialModuleAssociatedComplex_def {B : Type u} [CommRing B]
    (M : SimplicialObject (ModuleCat B)) :
    simplicialModuleAssociatedComplex B M =
      (alternatingFaceMapComplex (ModuleCat B)).obj M := sorry

-- Proof sketch: unfold `simplicialModuleTermwiseFlat`; the predicate is exactly the assertion
-- that each simplicial degree `M_n` is a flat `B`-module.
/-- Termwise flatness means flatness in every simplicial degree. -/
theorem simplicialModuleTermwiseFlat_iff {B : Type u} [CommRing B]
    (M : SimplicialObject (ModuleCat B)) :
    simplicialModuleTermwiseFlat B M ↔
      ∀ n : ℕ, Module.Flat B (M _⦋n⦌) := sorry

-- Proof sketch: specialize Lemma `21.39.10` to `\mathcal C = \Delta`, where `L\pi_!` is computed
-- by the alternating face map complex. Termwise flatness identifies the derived tensor products
-- with ordinary tensor products, and the resulting comparison map is the simplicial
-- Eilenberg-Zilber quasi-isomorphism.
/-- Remark 21.39.11 (Simplicial modules): if `M_•` and `M'_•` are termwise flat simplicial
`B`-modules, then the associated complex of their pointwise tensor product is quasi-isomorphic to
the total tensor product of the associated complexes `s(M_•)` and `s(M'_•)`. -/
theorem exists_quasiIso_simplicialModuleAssociatedComplex_tensor_of_termwiseFlat
    {B : Type u} [CommRing B]
    (M M' : SimplicialObject (ModuleCat B))
    (hM : simplicialModuleTermwiseFlat B M)
    (hM' : simplicialModuleTermwiseFlat B M') :
    ∃ α : simplicialModuleAssociatedComplex B (M ⊗ M') ⟶
        simplicialModuleAssociatedComplex B M ⊗ simplicialModuleAssociatedComplex B M',
      QuasiIso α := sorry

end CategoryTheory

/-! ### Lemma_21_39_12 (from Chap21) -/
open CategoryTheory Opposite

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory.ModulesOnCategory

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{max u v})
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

/-- The `RingCat`-valued structure sheaf on a category, viewed through the chaotic topology. -/
private abbrev chaoticRingSheaf :
    Sheaf (⊥ : GrothendieckTopology C) RingCat.{max u v} :=
  (sheafCompose (⊥ : GrothendieckTopology C) (forget₂ CommRingCat RingCat)).obj 𝒪

/-- The category `\mathrm{Mod}(\mathcal O)` of `\mathcal O`-modules on the chaotic site. -/
private abbrev moduleOnCategory :=
  SheafOfModules (chaoticRingSheaf 𝒪)

variable {𝒪' : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{max u v}}
variable [Abelian (moduleOnCategory 𝒪)]

/-- The target structure sheaf `\mathcal O'`, regarded by restriction of scalars as an
`\mathcal O`-module. -/
private abbrev targetAsSourceModule (α : 𝒪 ⟶ 𝒪') :
    moduleOnCategory 𝒪 :=
  (SheafOfModules.restrictScalars
      ((sheafCompose (⊥ : GrothendieckTopology C) (forget₂ CommRingCat RingCat)).map α)).obj
    (SheafOfModules.unit (chaoticRingSheaf 𝒪'))

-- Proof sketch: resolve `K` by complexes built from the flat generators `j_{U!}\mathcal O_U`,
-- compare the chosen derived lower shriek of `K` with the chosen derived lower shriek of
-- `K \otimes_{\mathcal O}^{\mathbf L} \mathcal O'`, and use the hypothesis that the structure
-- module map becomes an isomorphism after `L\pi_!` to descend the comparison from the generators
-- to all of `D(\mathcal O)`.
/-- Lemma 21.39.12: for a category with the chaotic topology and a morphism of sheaves of rings
`\mathcal O \to \mathcal O'`, if the induced map
`L\pi_!(\mathcal O) \to L\pi_!(\mathcal O')` is an isomorphism, then every object `K` of
`D(\mathcal O)` has the same derived lower shriek as its derived tensor product
`K \otimes_{\mathcal O}^{\mathbf L} \mathcal O'`. Here `structureModuleMap` is the chosen
`\mathcal O`-linear realization of the ring map on unit modules, and the functors
`derivedLowerShriek` and `derivedTensorWithStructureMap` are the chosen models of these two
derived constructions. -/
lemma derivedLowerShriek_isomorphic_after_tensor_structureSheafChange
    (α : 𝒪 ⟶ 𝒪')
    (structureModuleMap :
      SheafOfModules.unit (chaoticRingSheaf 𝒪) ⟶ targetAsSourceModule 𝒪 α)
    (derivedLowerShriek :
      DerivedCategory (moduleOnCategory 𝒪) ⥤ DerivedCategory AddCommGrpCat.{max u v})
    (derivedTensorWithStructureMap :
      DerivedCategory (moduleOnCategory 𝒪) ⥤ DerivedCategory (moduleOnCategory 𝒪))
    (hα : IsIso
      (derivedLowerShriek.map
        ((DerivedCategory.singleFunctor (moduleOnCategory 𝒪) (0 : ℤ)).map
          structureModuleMap)))
    (K : DerivedCategory (moduleOnCategory 𝒪)) :
    IsIsomorphic
      (derivedLowerShriek.obj K)
      (derivedLowerShriek.obj (derivedTensorWithStructureMap.obj K)) := sorry

end CategoryTheory.ModulesOnCategory
