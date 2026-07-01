import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u v' u'

namespace CategoryTheory

/- Domain-style sampling for Definition 25.2.1:
- primary domain: arbitrary type-indexed families of objects in a category and their
  componentwise morphisms;
- sampled declarations:
  `CategoryTheory.Over`,
  `CategoryTheory.Over.map`,
  `CategoryTheory.Over.forget`,
  `CategoryTheory.Sigma.desc`;
- best owner abstraction: `SemiRepresentableFamily C` itself. The sigma-category owner is too
  small because morphisms there do not allow retargeting indices along an arbitrary function, while
  the slice-category owners only supply fixed-target bridge/view API;
- primitive data: an indexing type together with its object family `index → C`;
- derived API: the category structure, componentwise functorial action `map`, the fixed-target
  bridge/view `Over X` with its indexed-arrow constructor `ofArrows`, and the forgetful functor
  `Over.forget : SR(C, X) ⥤ SR(C)`.

Source/core/bridge triage:
- `source-facing`: `SemiRepresentableFamily C`;
- `core/canonical`: the componentwise functorial owner `SemiRepresentableFamily.map`;
- `bridge/view`: `SemiRepresentableFamily.Over X`, `SemiRepresentableFamily.Over.ofArrows`, and
  the fixed-target forgetful functor induced by `CategoryTheory.Over.forget`.
-/

/-- Definition 25.2.1: `SR(C)` is the category whose objects are families of objects of `C`
indexed by an arbitrary type. -/
structure SemiRepresentableFamily (C : Type u) [Category.{v} C] where
  /-- The indexing type of the family. -/
  index : Type w
  /-- The object of `C` attached to each index. -/
  obj : index → C

namespace SemiRepresentableFamily

scoped notation "SR(" C ")" => _root_.CategoryTheory.SemiRepresentableFamily C

end SemiRepresentableFamily

open scoped CategoryTheory.SemiRepresentableFamily

namespace SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

/-- A morphism of semi-representable families is a map on indices together with a component
morphism in `C` for each source index. -/
structure Hom (U V : SemiRepresentableFamily C) where
  /-- The induced map on the indexing types. -/
  α : U.index → V.index
  /-- The component morphism attached to each source index. -/
  f : ∀ i : U.index, U.obj i ⟶ V.obj (α i)

namespace Hom

def id (U : SemiRepresentableFamily C) : U.Hom U where
  α := fun i ↦ i
  f := fun i ↦ 𝟙 (U.obj i)

def comp {U V W : SemiRepresentableFamily C} (φ : U.Hom V) (ψ : V.Hom W) : U.Hom W where
  α := ψ.α ∘ φ.α
  f := fun i ↦ φ.f i ≫ ψ.f (φ.α i)

@[ext] theorem ext {U V : SemiRepresentableFamily C} {φ ψ : U.Hom V}
    (hα : φ.α = ψ.α) (hf : ∀ i, HEq (φ.f i) (ψ.f i)) :
    φ = ψ := by
  cases φ with
  | mk αφ fφ =>
      cases ψ with
      | mk αψ fψ =>
          cases hα
          have hf' : fφ = fψ := by
            funext i
            exact eq_of_heq (hf i)
          cases hf'
          rfl

end Hom

/-- Semi-representable families form a category by composing index maps and component morphisms. -/
instance instCategory : Category (SemiRepresentableFamily C) where
  Hom U V := Hom U V
  id := Hom.id
  comp φ ψ := Hom.comp φ ψ
  id_comp := by
    intro X Y f
    refine Hom.ext (by funext i; rfl) ?_
    intro i
    simp [Hom.comp, Hom.id]
  comp_id := by
    intro X Y f
    refine Hom.ext (by funext i; rfl) ?_
    intro i
    simp [Hom.comp, Hom.id]
  assoc := by
    intro W X Y Z f g h
    refine Hom.ext (by funext i; rfl) ?_
    intro i
    simp [Hom.comp, Category.assoc]

/-- Applying a functor componentwise to a semi-representable family. -/
def map {D : Type u'} [Category.{v'} D] (F : C ⥤ D) :
    SemiRepresentableFamily C ⥤ SemiRepresentableFamily D where
  obj U :=
    { index := U.index
      obj := fun i ↦ F.obj (U.obj i) }
  map φ :=
    { α := φ.α
      f := fun i ↦ F.map (φ.f i) }
  map_id := by
    intro X
    refine Hom.ext rfl ?_
    intro i
    exact heq_of_eq (F.map_id (X.obj i))
  map_comp := by
    intro X Y Z φ ψ
    refine Hom.ext rfl ?_
    intro i
    exact heq_of_eq (F.map_comp (φ.f i) (ψ.f (φ.α i)))

@[simp] theorem map_obj_obj {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    (U : SemiRepresentableFamily C) (i : U.index) :
    ((map F).obj U).obj i = F.obj (U.obj i) :=
  rfl

/-- For `X : C`, the category `SR(C, X)` of semi-representable objects over `X` is `SR(C / X)`. -/
abbrev Over (X : C) :=
  SR(CategoryTheory.Over X)

end SemiRepresentableFamily

namespace SemiRepresentableFamily

scoped syntax "SR(" term ", " term ")" : term

scoped macro_rules
  | `(SR($_, $x)) => `(SemiRepresentableFamily.Over $x)

end SemiRepresentableFamily

namespace SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

namespace Over

/-- The fixed-target family over `X` defined by an indexed family of arrows `π i : Uᵢ i ⟶ X`. -/
abbrev ofArrows {X : C} {I : Type w} (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ X) : SR(C, X) where
  index := I
  obj := fun i ↦ CategoryTheory.Over.mk (π i)

/-- Forgetting the structure maps to `X` sends a family in `SR(C, X)` to its underlying family in
`SR(C)`. -/
def forget {X : C} : SR(C, X) ⥤ SR(C) :=
  SemiRepresentableFamily.map (CategoryTheory.Over.forget X)

@[simp] theorem forget_obj_obj {X : C} (K : SR(C, X)) (i : K.index) :
    (forget.obj K).obj i = (K.obj i).left :=
  rfl

@[simp] theorem forget_map_α {X : C} {K L : SR(C, X)} (φ : K ⟶ L) :
    (forget.map φ).α = φ.α :=
  rfl

@[simp] theorem forget_map_f {X : C} {K L : SR(C, X)} (φ : K ⟶ L) (i : K.index) :
    (forget.map φ).f i = (φ.f i).left :=
  rfl

end Over
end SemiRepresentableFamily

end CategoryTheory
