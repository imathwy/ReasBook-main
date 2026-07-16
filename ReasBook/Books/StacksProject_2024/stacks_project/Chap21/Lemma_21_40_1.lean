import StacksProject_2024.stacks_project.Chap21.Example_21_39_3
import StacksProject_2024.stacks_project.Chap21.Lemma_21_38_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Functor.Fiber
open scoped CategoryTheory.CategoryHomology

noncomputable section

universe u v

namespace CategoryTheory
namespace FibredCategoryOver

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (P : FibredCategoryOver C)
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasWeakSheafify (inheritedTopology J P) AddCommGrpCat.{max u v}]
variable [∀ V : C, HasProjectiveResolutions ((P.p.Fiber V)ᵒᵖ ⥤ AddCommGrpCat.{max u v})]
variable [∀ ⦃U V : C⦄ (f : V ⟶ U), (fiberPullbackPrecomp P f).PreservesProjectiveObjects]

local notation "Jₚ" => inheritedTopology J P

/- Domain-style sampling for Lemma 21.40.1:
- primary domain: fiberwise category homology of abelian presheaves on a fibred category over a
  site;
- sampled owner declarations:
  `Functor.leftDerived`,
  `CategoryTheory.categoryHomologyMap`,
  `CategoryTheory.FibredCategoryOver.fiberPullbackPrecomp`,
  `CategoryTheory.FibredCategoryOver.fiberRestrictionPresheaf`;
- best owner abstraction: this file is a `source-facing` owner for the presheaf
  `V ↦ H_n(𝒞_V, ℱ|_{𝒞_V})`, built from the canonical derived-colimit
  surface `H_[n](C, ℱ)` and `fiberPullbackPrecomp`, so it should reuse those directly rather than
  duplicate the pullback-precomposition bridge locally;
- primitive data: a base object `V : C`, the restricted abelian presheaf
  `fiberRestrictionPresheaf P ℱ V` on the fiber, and the
  pullback functor on fibers induced by a morphism in `C`, together with its projective-
  preservation hypothesis on presheaf categories;
- derived API: the restriction maps on fiberwise homology, the resulting presheaf on `C`, and its
  sheafification.

Source/core/bridge triage:
- `source-facing`: `fiberCategoryHomologyPresheaf` and `fiberCategoryHomologySheaf`;
- `core/canonical`: the left derived colimit owner `(colim).leftDerived`;
- `bridge/view`: `fiberPullbackPrecomp`, `fiberRestrictionPresheaf`, and the comparison maps built
  from `colimit.pre`. -/

/-- The category homology `H_n(𝒞_V, ℱ|_{𝒞_V})` of the fiber over `V`.
This keeps the projective-resolution hypothesis internal to the bridge. -/
abbrev fiberCategoryHomology
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}) (V : C) (n : ℕ) :
    AddCommGrpCat.{max u v} :=
  let _ : HasColimitsOfShape (P.p.Fiber V)ᵒᵖ AddCommGrpCat.{max u v} := by infer_instance
  H_[n](P.p.Fiber V, fiberRestrictionPresheaf P ℱ V)

/-- The restriction map on fiberwise category homology induced by a morphism in the base site. -/
private abbrev fiberCategoryHomologyRestriction
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {U V : C} (f : V ⟶ U) (n : ℕ) :
    fiberCategoryHomology P ℱ U n ⟶ fiberCategoryHomology P ℱ V n :=
  let _ : HasColimitsOfShape (P.p.Fiber U)ᵒᵖ AddCommGrpCat.{max u v} := by infer_instance
  let _ : HasColimitsOfShape (P.p.Fiber V)ᵒᵖ AddCommGrpCat.{max u v} := by infer_instance
  categoryHomologyMap ((canonicalPullbackChoice P.p).pullbackFunctor f)
    (fiberRestrictionComparison P ℱ f) n

-- Proof sketch: for the identity arrow, the chosen pullback functor on the fiber is naturally
-- isomorphic to the identity, so both the map on left-derived colimits and the colimit
-- comparison reduce to identities.
/-- The fiberwise category-homology restriction is the identity on identity arrows. -/
private theorem fiberCategoryHomologyRestriction_id
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) (U : C) :
    fiberCategoryHomologyRestriction P ℱ (𝟙 U) n =
      𝟙 (fiberCategoryHomology P ℱ U n) :=
  sorry

-- Proof sketch: compose the pullback functors on fibers and compare the resulting projective
-- resolution models for homology. The functoriality of left-derived colimits and the cocycle
-- identity for `colimit.pre` give the stated composition law.
/-- Fiberwise category-homology restrictions respect composition in the base site. -/
private theorem fiberCategoryHomologyRestriction_comp
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    fiberCategoryHomologyRestriction P ℱ (g ≫ f) n =
      fiberCategoryHomologyRestriction P ℱ f n ≫
        fiberCategoryHomologyRestriction P ℱ g n := sorry

-- Proof sketch: after unop-ing arrows in `Cᵒᵖ`, this is exactly the composition formula for the
-- underlying restriction maps on fiberwise category homology.
/-- The morphism part of `fiberCategoryHomologyPresheaf` respects composition. -/
private theorem fiberCategoryHomologyPresheaf_map_comp
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ)
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    fiberCategoryHomologyRestriction P ℱ (f ≫ g).unop n =
      fiberCategoryHomologyRestriction P ℱ f.unop n ≫
        fiberCategoryHomologyRestriction P ℱ g.unop n := sorry

/-- The presheaf on the base site sending `V` to the category homology
`H_n(𝒞_V, ℱ|_{𝒞_V})`. -/
abbrev fiberCategoryHomologyPresheaf
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    Cᵒᵖ ⥤ AddCommGrpCat.{max u v} where
  obj V := fiberCategoryHomology P ℱ (unop V) n
  map f := fiberCategoryHomologyRestriction P ℱ f.unop n
  map_id V := fiberCategoryHomologyRestriction_id P ℱ n (unop V)
  map_comp f g := fiberCategoryHomologyPresheaf_map_comp P ℱ n f g

/-- The sheaf associated to the source-facing presheaf `L_[n,p](P, ℱ)`. -/
abbrev fiberCategoryHomologySheaf
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    Sheaf J AddCommGrpCat.{max u v} :=
  (presheafToSheaf J AddCommGrpCat.{max u v}).obj
    (fiberCategoryHomologyPresheaf P ℱ n)

namespace FibredCategoryOverFiberHomology

/- Textbook surface notation for the source-facing Chapter 21 owners
`L_[n,p](P, ℱ)` and `L_[n](J, P, ℱ)`. -/
scoped syntax:max "L_[" term:max ",p](" term ", " term ")" : term

scoped macro_rules
  | `(L_[$n,p]($P, $ℱ)) =>
      `(CategoryTheory.FibredCategoryOver.fiberCategoryHomologyPresheaf $P $ℱ $n)

scoped syntax:max "L_[" term:max "](" term ", " term ", " term ")" : term

scoped macro_rules
  | `(L_[$n]($J, $P, $ℱ)) =>
      `(CategoryTheory.FibredCategoryOver.fiberCategoryHomologySheaf $J $P $ℱ $n)

end FibredCategoryOverFiberHomology

open scoped FibredCategoryOverFiberHomology

/-- Bridge view: the fiberwise category-homology sheaf attached to an abelian sheaf on the total
site, obtained by forgetting to its underlying presheaf. -/
abbrev fiberCategoryHomologySheafOfSheaf
    (ℱ : Sheaf Jₚ AddCommGrpCat.{max u v}) (n : ℕ) :
    Sheaf J AddCommGrpCat.{max u v} :=
  L_[n](J, P, ℱ.1)

/-- The restriction of `toSheafify Jₚ ℱ` to the opposite of the fiber over `V`. -/
private abbrev fiberRestrictionToAssociatedAbelianSheaf
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}) (V : C) :
    fiberRestrictionPresheaf P ℱ V ⟶
      fiberRestrictionPresheaf P
        ((presheafToSheaf Jₚ AddCommGrpCat.{max u v}).obj ℱ).1 V :=
  Functor.whiskerLeft
    ((Functor.Fiber.fiberInclusion : P.p.Fiber V ⥤ P.S).op)
    (toSheafify Jₚ ℱ)

/-- The objectwise comparison on fiberwise category-homology presheaves induced by the
sheafification unit on the total site. -/
private abbrev fiberCategoryHomologyPresheaf_associatedAbelianSheafMapApp
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}) (V : Cᵒᵖ) (n : ℕ) :
    (L_[n,p](P, ℱ)).obj V ⟶
      (L_[n,p](P, ((presheafToSheaf Jₚ AddCommGrpCat.{max u v}).obj ℱ).1)).obj V :=
  let _ :
      HasColimitsOfShape (P.p.Fiber (unop V))ᵒᵖ AddCommGrpCat.{max u v} := by
    infer_instance
  categoryHomologyMap (𝟭 (P.p.Fiber (unop V)))
    (fiberRestrictionToAssociatedAbelianSheaf J P ℱ (unop V)) n

-- Proof sketch: naturality follows from functoriality of `categoryHomologyMap` for the identity
-- functor on each fiber and naturality of the sheafification unit `toSheafify Jₚ ℱ`.
/-- The objectwise comparison induced by sheafification is natural in the base object. -/
private theorem fiberCategoryHomologyPresheaf_associatedAbelianSheafMap_naturality
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (L_[n,p](P, ℱ)).map f ≫
        fiberCategoryHomologyPresheaf_associatedAbelianSheafMapApp J P ℱ V n =
      fiberCategoryHomologyPresheaf_associatedAbelianSheafMapApp J P ℱ U n ≫
        (L_[n,p](P, ((presheafToSheaf Jₚ AddCommGrpCat.{max u v}).obj ℱ).1)).map f := sorry

/-- The canonical comparison morphism on the source-facing homology presheaves, induced by the
sheafification unit on the total site. -/
abbrev fiberCategoryHomologyPresheaf_associatedAbelianSheafMap
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    L_[n,p](P, ℱ) ⟶
      L_[n,p](P, ((presheafToSheaf Jₚ AddCommGrpCat.{max u v}).obj ℱ).1) where
  app V := fiberCategoryHomologyPresheaf_associatedAbelianSheafMapApp J P ℱ V n
  naturality := fun {_ _} f ↦
    fiberCategoryHomologyPresheaf_associatedAbelianSheafMap_naturality J P ℱ n f

/-- The canonical sheaf-level comparison morphism in Lemma 21.40.1. -/
abbrev fiberCategoryHomologySheaf_associatedAbelianSheafHom
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    L_[n](J, P, ℱ) ⟶
      fiberCategoryHomologySheafOfSheaf J P
        ((presheafToSheaf Jₚ AddCommGrpCat.{max u v}).obj ℱ) n :=
  (presheafToSheaf J AddCommGrpCat.{max u v}).map
    (fiberCategoryHomologyPresheaf_associatedAbelianSheafMap J P ℱ n)

-- Proof sketch: the presheaf map above is locally bijective by the fiberwise projective-resolution
-- description of category homology and the local exactness properties of `toSheafify Jₚ ℱ`; hence
-- its sheafification is an isomorphism.
/-- Lemma 21.40.1: for an abelian presheaf `ℱ` on the total category of a fibred category over
the base site `J`, the canonical comparison
`L_[n](J, P, ℱ) ⟶ L_[n](J, P, ((presheafToSheaf Jₚ AddCommGrpCat).obj ℱ).1)` is an isomorphism. -/
@[stacks 08PI]
theorem fiberCategoryHomologySheaf_associatedAbelianSheafHom_isIso
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    IsIso (fiberCategoryHomologySheaf_associatedAbelianSheafHom J P ℱ n) := sorry

/-- Canonical instance companion for the comparison morphism in Lemma 21.40.1. -/
instance fiberCategoryHomologySheaf_associatedAbelianSheafHom.instIsIso
    (ℱ : P.Sᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    IsIso (fiberCategoryHomologySheaf_associatedAbelianSheafHom J P ℱ n) :=
  fiberCategoryHomologySheaf_associatedAbelianSheafHom_isIso J P ℱ n

end

end FibredCategoryOver
end CategoryTheory
