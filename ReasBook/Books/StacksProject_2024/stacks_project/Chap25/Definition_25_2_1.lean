import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u v' u'

namespace CategoryTheory

open CategoryTheory.Limits

/- Domain-style sampling for Definition 25.2.1:
- primary domain: arbitrary type-indexed families of objects in a category and their
  componentwise morphisms;
- sampled declarations:
  `CategoryTheory.Limits.FormalCoproduct`,
  `CategoryTheory.Over`,
  `CategoryTheory.Over.forget`,
  `CategoryTheory.Sigma.desc`;
- best owner abstraction: the source-facing Stacks vocabulary `SemiRepresentableFamily C` is
  definitionally the canonical mathlib owner `CategoryTheory.Limits.FormalCoproduct C`;
- primitive data: an indexing type together with its object family `index → C`;
- derived API: the Stacks-facing notation `SR(C)`, the source vocabulary `index`, the
  componentwise functorial action `map`, the fixed-target bridge/view `Over X`, the indexed-arrow
  constructor `Over.ofArrows`, and the forgetful functor `Over.forget : SR(C, X) ⥤ SR(C)`.

Source/core/bridge triage:
- `source-facing`: `SemiRepresentableFamily C`;
- `core/canonical`: `CategoryTheory.Limits.FormalCoproduct C`;
- `bridge/view`: `SemiRepresentableFamily.Over X`, `SemiRepresentableFamily.map`,
  `SemiRepresentableFamily.Over.ofArrows`, and `SemiRepresentableFamily.Over.forget`.
-/

/-
Definition 25.2.1: `SR(C)` is the category whose objects are families of objects of `C`
indexed by an arbitrary type. This is exactly mathlib's canonical formal-coproduct owner.
-/
abbrev SemiRepresentableFamily (C : Type u) [Category.{v} C] := FormalCoproduct.{w} C

namespace SemiRepresentableFamily

scoped notation "SR(" C ")" => _root_.CategoryTheory.SemiRepresentableFamily C

end SemiRepresentableFamily

open scoped CategoryTheory.SemiRepresentableFamily

namespace SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

/-- The source-facing index type of a semi-representable family. -/
abbrev index (K : SR(C)) : Type w := K.I

/-- The Stacks-facing view of a semi-representable family as the canonical formal coproduct. -/
abbrev toFormalCoproduct : SR(C) ⥤ FormalCoproduct.{w} C :=
  𝟭 _

/-- The canonical formal coproduct is already a semi-representable family. -/
abbrev ofFormalCoproduct : FormalCoproduct.{w} C ⥤ SR(C) :=
  𝟭 _

/-- Applying a functor componentwise to a semi-representable family. -/
def map {D : Type u'} [Category.{v'} D] (F : C ⥤ D) :
    SR(C) ⥤ SR(D) where
  obj U := ⟨U.I, fun i ↦ F.obj (U.obj i)⟩
  map φ := ⟨φ.f, fun i ↦ F.map (φ.φ i)⟩
  map_id := by
    intro U
    refine FormalCoproduct.hom_ext (by funext i; rfl) ?_
    intro i
    simp
  map_comp := by
    intro U V W φ ψ
    refine FormalCoproduct.hom_ext (by funext i; rfl) ?_
    intro i
    simp [Functor.map_comp]

@[simp] theorem map_obj_obj {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    (U : SR(C)) (i : U.index) :
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
abbrev ofArrows {X : C} {I : Type w} (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ X) : SR(C, X) :=
  ⟨I, fun i ↦ CategoryTheory.Over.mk (π i)⟩

/-- The fixed-target formal-coproduct view is definitionally the same canonical owner. -/
abbrev toFormalCoproduct {X : C} :
    SR(C, X) ⥤ FormalCoproduct.{w} (CategoryTheory.Over X) :=
  𝟭 _

/-- The canonical formal coproduct in `Over X` is already a fixed-target family. -/
abbrev ofFormalCoproduct {X : C} :
    FormalCoproduct.{w} (CategoryTheory.Over X) ⥤ SR(C, X) :=
  𝟭 _

/-- Forgetting the structure maps to `X` sends a family in `SR(C, X)` to its underlying family in
`SR(C)`. -/
def forget {X : C} : SR(C, X) ⥤ SR(C) :=
  SemiRepresentableFamily.map (CategoryTheory.Over.forget X)

@[simp] theorem forget_obj_obj {X : C} (K : SR(C, X)) (i : K.index) :
    (forget.obj K).obj i = (K.obj i).left :=
  rfl

@[simp] theorem forget_map_f {X : C} {K L : SR(C, X)} (φ : K ⟶ L) :
    (forget.map φ).f = φ.f :=
  rfl

@[simp] theorem forget_map_φ {X : C} {K L : SR(C, X)} (φ : K ⟶ L) (i : K.index) :
    (forget.map φ).φ i = (φ.φ i).left :=
  rfl

end Over
end SemiRepresentableFamily

end CategoryTheory
