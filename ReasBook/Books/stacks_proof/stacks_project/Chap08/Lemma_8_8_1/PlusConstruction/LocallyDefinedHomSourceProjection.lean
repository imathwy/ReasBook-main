import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomSourceCategoryLaws

universe u v uX vX

namespace CategoryTheory

open Bicategory
open FibredCategoryMor
open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace FibredCategoryMor

namespace LocallyDefinedHomTotal

/-- Source stage 2 projection for the locally-defined-Hom total category, using the literal
source identity representative from the Stacks construction.

This is intentionally kept separate from the old ordinary-identity surface.  The projection
itself has no owner ambiguity: the base arrow of a locally-defined morphism is its first
component, the source identity has base `𝟙`, and composition has base the composite. -/
noncomputable def sourceProjection
    (X : FibredCategoryOver.{u, v, uX, vX} C) :
    letI := sourceCategory (J := J) X
    LocallyDefinedHomTotal (J := J) X ⥤ C := by
  letI := sourceCategory (J := J) X
  exact
    { obj := fun x => projectionObj (J := J) x
      map := fun {x y} f => projectionMap (J := J) f
      map_id := by
        intro x
        change (sourceIdentityHomToLocallyDefinedHom (J := J) X x.obj).1 =
          𝟙 (X.p.obj x.obj)
        exact sourceIdentityHomToLocallyDefinedHom_base (J := J) X x.obj
      map_comp := by
        intro x y z f g
        exact LocallyDefinedHom.comp_base (J := J) f g }

@[simp]
theorem sourceProjection_obj
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    (x : LocallyDefinedHomTotal (J := J) X) :
    letI := sourceCategory (J := J) X
    (sourceProjection (J := J) X).obj x = X.p.obj x.obj := by
  letI := sourceCategory (J := J) X
  rfl

@[simp]
theorem sourceProjection_map
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    {x y : LocallyDefinedHomTotal (J := J) X} :
    letI := sourceCategory (J := J) X
    ∀ f : x ⟶ y,
    (sourceProjection (J := J) X).map f = f.1 := by
  letI := sourceCategory (J := J) X
  intro f
  rfl

/-- The source stage 2 based-category surface attached to locally-defined morphisms.

The next owner bridge is not folded in here: constructing the canonical old-object functor
`X ⟶ sourceBasedCategory X` still needs the explicit comparison between the ordinary identity
representative and the literal source identity representative. -/
noncomputable def sourceBasedCategory
    (X : FibredCategoryOver.{u, v, uX, vX} C) : BasedCategory C := by
  letI := sourceCategory (J := J) X
  exact BasedCategory.ofFunctor (sourceProjection (J := J) X)

/-- Source-faithful frontier for upgrading the locally-defined-Hom projection to an actual
fibred category.  This names the remaining cartesian-lift obligation instead of hiding it behind
a definitional equality. -/
structure SourceProjectionFiberedFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- Pullbacks in the source stage 2 projection are represented by the Stacks construction's
  pullback of a locally-defined morphism along a base arrow. -/
  isFibered :
    letI := sourceCategory (J := J) X
    (sourceProjection (J := J) X).IsFibered

/-- If the source stage 2 projection has its cartesian-lift calculation, it bundles as a fibred
category over the site base. -/
noncomputable def sourceFibredCategoryOfFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    (H : @SourceProjectionFiberedFrontier C _ J X) :
    FibredCategoryOver C := by
  letI := sourceCategory (J := J) X
  letI : (sourceProjection (J := J) X).IsFibered := H.isFibered
  exact FibredCategoryOver.ofFunctor (sourceProjection (J := J) X)

/-- Source-faithful frontier for the old-object comparison into the stage 2 category.

The identity field is exactly the known owner obstruction: the ordinary representative of
`𝟙 x` and the literal source identity representative should be proved equal, but this should not
be replaced by `rfl`.  The composition field is the corresponding functoriality check for
ordinary arrows represented on the trivial cover. -/
structure OldObjectComparisonFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- Ordinary identity representative equals the literal source identity representative. -/
  identityBridge :
    ∀ x : X.S,
      ordinaryHomToLocallyDefinedHom (J := J) X (𝟙 x) =
        sourceIdentityHomToLocallyDefinedHom (J := J) X x
  /-- Ordinary representatives are compatible with composition in the source category. -/
  compositionBridge :
    ∀ ⦃x y z : X.S⦄ (f : x ⟶ y) (g : y ⟶ z),
      ordinaryHomToLocallyDefinedHom (J := J) X (f ≫ g) =
        LocallyDefinedHom.comp (J := J)
          (ordinaryHomToLocallyDefinedHom (J := J) X f)
          (ordinaryHomToLocallyDefinedHom (J := J) X g)

end LocallyDefinedHomTotal

end FibredCategoryMor

end CategoryTheory
