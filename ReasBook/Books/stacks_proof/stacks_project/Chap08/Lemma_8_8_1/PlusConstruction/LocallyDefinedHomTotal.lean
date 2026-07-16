import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomIdentity

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

/-- Helper for Chap08 Lemma 8 8 1, source stage 2.4: the total object wrapper for the
locally-defined-Hom construction.  Objects are unchanged from `X`; the wrapper lets us attach the
new Hom surface without changing the existing category structure on `X.S`. -/
structure LocallyDefinedHomTotal
    (J : GrothendieckTopology C) (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- The underlying object of the original total category. -/
  obj : X.S

namespace LocallyDefinedHomTotal

instance (X : FibredCategoryOver.{u, v, uX, vX} C) :
    CoeOut (LocallyDefinedHomTotal (J := J) X) X.S :=
  ⟨LocallyDefinedHomTotal.obj⟩

/-- The unchanged-object inclusion into the locally-defined-Hom total surface. -/
abbrev ofObj (X : FibredCategoryOver.{u, v, uX, vX} C) (x : X.S) :
    LocallyDefinedHomTotal (J := J) X :=
  ⟨x⟩

/-- Objects are unchanged in the locally-defined-Hom surface. -/
def objectEquiv (X : FibredCategoryOver.{u, v, uX, vX} C) :
    LocallyDefinedHomTotal (J := J) X ≃ X.S where
  toFun x := x.obj
  invFun x := ofObj (J := J) X x
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    rfl

/-- The category-structure data for the source construction's `S²`: locally-defined morphisms
with the identity and composition described in the text.  The full `Category` instance is kept
separate, since its laws require the explicit trivial-cover and triple-cover proofs. -/
noncomputable instance categoryStruct (X : FibredCategoryOver.{u, v, uX, vX} C) :
    CategoryStruct (LocallyDefinedHomTotal (J := J) X) where
  Hom x y := locallyDefinedHom (J := J) X x.obj y.obj
  id x := locallyDefinedHomId (J := J) X x.obj
  comp f g := LocallyDefinedHom.comp (J := J) f g

/-- Object function of the source construction's projection `p²`. -/
@[simp]
def projectionObj {X : FibredCategoryOver.{u, v, uX, vX} C}
    (x : LocallyDefinedHomTotal (J := J) X) : C :=
  X.p.obj x.obj

/-- Arrow function of the source construction's projection `p²`, before the full category laws
are installed. -/
def projectionMap {X : FibredCategoryOver.{u, v, uX, vX} C}
    {x y : LocallyDefinedHomTotal (J := J) X} (f : x ⟶ y) :
    projectionObj (J := J) x ⟶ projectionObj (J := J) y :=
  f.1

/-- The projection sends the locally-defined identity to the base identity. -/
@[simp]
theorem projectionMap_id {X : FibredCategoryOver.{u, v, uX, vX} C}
    (x : LocallyDefinedHomTotal (J := J) X) :
    projectionMap (J := J) (𝟙 x) = 𝟙 (projectionObj (J := J) x) := by
  exact locallyDefinedHomId_base (J := J) X x.obj

/-- The projection sends locally-defined composition to composition of base arrows. -/
@[simp]
theorem projectionMap_comp {X : FibredCategoryOver.{u, v, uX, vX} C}
    {x y z : LocallyDefinedHomTotal (J := J) X} (f : x ⟶ y) (g : y ⟶ z) :
    projectionMap (J := J) (f ≫ g) =
      projectionMap (J := J) f ≫ projectionMap (J := J) g := by
  exact LocallyDefinedHom.comp_base (J := J) f g

/-- The source construction's `G²` on arrows, before the full functor laws are installed:
ordinary arrows are represented on the trivial cover. -/
noncomputable def ofHom {X : FibredCategoryOver.{u, v, uX, vX} C}
    {x y : LocallyDefinedHomTotal (J := J) X} (f : x.obj ⟶ y.obj) :
    x ⟶ y :=
  ordinaryHomToLocallyDefinedHom (J := J) X f

/-- The source construction's `G²` is the identity on objects. -/
@[simp]
theorem ofObj_obj (X : FibredCategoryOver.{u, v, uX, vX} C) (x : X.S) :
    (ofObj (J := J) X x).obj = x :=
  rfl

/-- The ordinary-arrow representative has exactly the original base arrow. -/
@[simp]
theorem projectionMap_ofHom {X : FibredCategoryOver.{u, v, uX, vX} C}
    {x y : LocallyDefinedHomTotal (J := J) X} (f : x.obj ⟶ y.obj) :
    projectionMap (J := J) (ofHom (J := J) f) = X.p.map f :=
  rfl

/-- Base-arrow compatibility of `G²` with ordinary identities. -/
theorem ofHom_id_base {X : FibredCategoryOver.{u, v, uX, vX} C} (x : X.S) :
    projectionMap (J := J)
        (ofHom (J := J) (X := X)
          (x := ofObj (J := J) X x) (y := ofObj (J := J) X x) (𝟙 x)) =
      𝟙 (X.p.obj x) := by
  simp

/-- `G²` sends ordinary identities to the locally-defined identities by definition. -/
@[simp]
theorem ofHom_id {X : FibredCategoryOver.{u, v, uX, vX} C} (x : X.S) :
    ofHom (J := J) (X := X)
        (x := ofObj (J := J) X x) (y := ofObj (J := J) X x) (𝟙 x) =
      𝟙 (ofObj (J := J) X x) :=
  rfl

/-- Base-arrow compatibility of `G²` with ordinary composition. -/
theorem ofHom_comp_base {X : FibredCategoryOver.{u, v, uX, vX} C}
    {x y z : X.S} (f : x ⟶ y) (g : y ⟶ z) :
    projectionMap (J := J)
        (ofHom (J := J) (X := X)
          (x := ofObj (J := J) X x) (y := ofObj (J := J) X z) (f ≫ g)) =
      projectionMap (J := J)
          (ofHom (J := J) (X := X)
            (x := ofObj (J := J) X x) (y := ofObj (J := J) X y) f) ≫
        projectionMap (J := J)
          (ofHom (J := J) (X := X)
            (x := ofObj (J := J) X y) (y := ofObj (J := J) X z) g) := by
  simp

end LocallyDefinedHomTotal
end FibredCategoryMor

end CategoryTheory
