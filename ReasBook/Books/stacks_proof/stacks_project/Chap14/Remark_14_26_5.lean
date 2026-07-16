import Mathlib
import stacks_proof.stacks_project.Chap14.Definition_14_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Remark 14.26.5:
- primary domain: simplicial homotopy and the quotient category determined by the zigzag homotopy
  relation on morphisms of simplicial objects;
- inspected same-kind declarations:
  `CategoryTheory.SimplicialObject.Homotopic.precomp`,
  `CategoryTheory.SimplicialObject.Homotopic.postcomp`,
  `CategoryTheory.Quotient.functor`,
  `HomologicalComplex.HomotopyCategory.quotient`;
- best owner abstraction: the source-facing owner is the homotopy category
  `CategoryTheory.SimplicialObject.HomotopyCategory`, with the canonical core presentation
  `CategoryTheory.Quotient (homotopic C)` built from the hom relation induced by `Homotopic`;
- primitive data: the zigzag homotopy relation `Homotopic` on each hom-set;
- derived API: the induced `HomRel`, its congruence instance, the quotient category, and the
  canonical quotient functor.

Source/core/bridge triage:
- `source-facing`: `HomotopyCategory C` and its quotient functor, the simplicial homotopy category
  from the remark;
- `core/canonical`: `CategoryTheory.Quotient (homotopic C)`;
- `bridge/view`: `homotopic C : HomRel (SimplicialObject C)`, packaging `Homotopic` for the
  canonical quotient construction.
-/
/-- The hom relation on simplicial objects given by the zigzag simplicial homotopy relation. -/
abbrev homotopic (C : Type u) [Category.{v} C] : HomRel (SimplicialObject C) :=
  fun _ _ ↦ Homotopic

/-- Simplicial homotopy is a congruence relation on morphisms of simplicial objects. -/
instance homotopic_congruence (C : Type u) [Category.{v} C] :
    Congruence (homotopic C) where
  equivalence :=
    { refl := Homotopic.refl
      symm := fun h ↦ h.symm
      trans := fun h k ↦ h.trans k }
  comp_left := by
    intro _ _ _ f _ _ h
    exact h.precomp f
  comp_right := by
    intro _ _ _ _ _ g h
    exact h.postcomp g

/-- Remark 14.26.5: the homotopy category `hSimp(C)` of simplicial objects in `C`, with the same
objects as `SimplicialObject C` and morphisms represented by homotopy classes. -/
@[stacks 08RJ]
abbrev HomotopyCategory (C : Type u) [Category.{v} C] : Type (max u v) :=
  CategoryTheory.Quotient (homotopic C)

scoped notation "hSimp(" C:arg ")" => HomotopyCategory C

namespace HomotopyCategory

/-- The canonical quotient functor from simplicial objects to their homotopy category
`hSimp(C)`. -/
abbrev quotient (C : Type u) [Category.{v} C] :
    SimplicialObject C ⥤ HomotopyCategory C :=
  CategoryTheory.Quotient.functor (homotopic C)

/-- Every object of `hSimp(C)` is represented by a simplicial object of `C`. -/
lemma quotient_obj_surjective (X : HomotopyCategory C) :
    ∃ Y : SimplicialObject C, (quotient C).obj Y = X :=
  ⟨_, rfl⟩

/-- The underlying simplicial object of the image of `X` in `hSimp(C)` is `X` itself. -/
theorem quotient_obj_as (X : SimplicialObject C) :
    ((quotient C).obj X).as = X :=
  rfl

-- Proof sketch: `hSimp(C)` is the categorical quotient by the congruence `homotopic C`, so
-- equality after applying the quotient functor is exactly the quotient relation.
/-- Two morphisms of simplicial objects become equal in `hSimp(C)` exactly when they are
homotopic. -/
theorem map_eq_iff_homotopic {X Y : SimplicialObject C} (f g : X ⟶ Y) :
    (quotient C).map f = (quotient C).map g ↔ Homotopic f g := by
  simpa [homotopic] using
    (CategoryTheory.Quotient.functor_map_eq_iff (homotopic C) f g)

-- Proof sketch: the quotient functor to `hSimp(C)` identifies morphisms related by the defining
-- congruence `homotopic C`, so apply the quotient soundness statement for the relation `Homotopic`.
/-- Homotopic morphisms of simplicial objects define the same morphism in the homotopy category
`hSimp(C)`. -/
theorem eq_of_homotopic {X Y : SimplicialObject C} (f g : X ⟶ Y) (h : Homotopic f g) :
    (quotient C).map f = (quotient C).map g :=
  CategoryTheory.Quotient.sound (homotopic C) h

instance (C : Type u) [Category.{v} C] : (quotient C).Full :=
  Quotient.full_functor (homotopic C)

instance (C : Type u) [Category.{v} C] : (quotient C).EssSurj :=
  Quotient.essSurj_functor (homotopic C)

end HomotopyCategory

end CategoryTheory.SimplicialObject
