import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

-- Declarations for this item will be appended below by the statement pipeline.

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
