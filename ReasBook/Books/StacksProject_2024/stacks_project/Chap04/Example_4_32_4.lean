import Mathlib
import StacksProject_2024.stacks_project.Chap04.Lemma_4_32_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryOver
open scoped CategoricalPullback

namespace CategoryTheory

/-
Domain-style sampling for Example 4.32.4:
- primary domain: comparison between the categorical pullback of functors and the canonical
  `2`-fibre product in `Cat/C`;
- owner abstractions:
  `CategoricalPullback` for the pullback of plain categories,
  `CategoryOver` for categories over a fixed base,
  `BasedCategory.toBase` for the canonical morphism from an object of `Cat/C` to the base object,
  `CategoryOver.explicitTwoFibreProduct` for the canonical pullback object in `Cat/C`;
- primitive data: the unique functor from the one-point category to the one-object two-arrow
  groupoid, and the corresponding object of `Cat/exampleTwoArrowGroupoid`;
- derived API: the concrete discrete-category descriptions of the two pullback constructions,
  together with the resulting inequivalence companion.

Source/core/bridge triage:
- `source-facing`: the concrete descriptions of the two pullback constructions in the example;
- `core/canonical`: `CategoricalPullback` and `explicitTwoFibreProduct`;
- `bridge/view`: the inequivalence comparison theorem deduced from those concrete descriptions. -/

/-- The two-element group used to realize the one-object groupoid with two arrows. -/
abbrev exampleTwoArrowGroup := Multiplicative (ZMod 2)

/-- The groupoid with one object and two arrows from Example 4.32.4. -/
abbrev exampleTwoArrowGroupoid : Type := SingleObj exampleTwoArrowGroup

/-- The unique object of the one-object two-arrow groupoid. -/
private abbrev exampleBaseObject : exampleTwoArrowGroupoid :=
  SingleObj.star exampleTwoArrowGroup

/-- The discrete category with one object from Example 4.32.4. -/
abbrev exampleOnePointCategory : Type := Discrete PUnit

/-- The unique functor from the one-point discrete category to the two-arrow groupoid. -/
abbrev exampleOnePointToTwoArrowGroupoid :
    exampleOnePointCategory ⥤ exampleTwoArrowGroupoid :=
  Functor.fromPUnit exampleBaseObject

/-- The categorical pullback of the example cospan, viewed only as a cospan of categories. -/
private abbrev exampleCategoricalPullback :=
  exampleOnePointToTwoArrowGroupoid ⊡ exampleOnePointToTwoArrowGroupoid

/-- The one-point category viewed as an object of `Cat/exampleTwoArrowGroupoid`. -/
abbrev exampleOnePointOverGroupoid : CategoryOver exampleTwoArrowGroupoid :=
  BasedCategory.ofFunctor exampleOnePointToTwoArrowGroupoid

/-- The underlying category of the canonical `2`-fibre product in
`Cat/exampleTwoArrowGroupoid` for Example 4.32.4. -/
private abbrev exampleCategoryOverPullback :=
  (explicitTwoFibreProduct exampleOnePointOverGroupoid.toBase exampleOnePointOverGroupoid.toBase).obj

/-- The unique object of the one-point discrete category. -/
private abbrev exampleOnePointObject : exampleOnePointCategory :=
  Discrete.mk PUnit.unit

/-- The unique object of the fibre of the one-point functor over the unique base object. -/
private abbrev exampleOnePointLift :
    Functor.Fiber exampleOnePointOverGroupoid.p exampleBaseObject :=
  Functor.Fiber.mk (show exampleOnePointOverGroupoid.p.obj exampleOnePointObject = exampleBaseObject from rfl)

/-- The unique object of the fibre of the identity functor over the unique base object. -/
private abbrev exampleIdentityLift :
    Functor.Fiber (𝟭 exampleTwoArrowGroupoid) exampleBaseObject :=
  Functor.Fiber.mk (show (𝟭 exampleTwoArrowGroupoid).obj exampleBaseObject = exampleBaseObject from rfl)

/-- The canonical object of the `2`-fibre product in `Cat/exampleTwoArrowGroupoid`. -/
private abbrev exampleCategoryOverPullbackPoint : exampleCategoryOverPullback :=
  { U := exampleBaseObject
    obj :=
      { fst := exampleOnePointLift
        snd := exampleOnePointLift
        iso := Iso.refl exampleIdentityLift } }

/-- The object of the categorical pullback determined by a chosen automorphism of the unique
object of the two-arrow groupoid. -/
private noncomputable def exampleCategoricalPullbackFromArrow
    (g : exampleTwoArrowGroup) : exampleCategoricalPullback :=
  { fst := exampleOnePointObject
    snd := exampleOnePointObject
    iso := asIso g }

-- Proof sketch: the structural isomorphism of `exampleCategoricalPullbackFromArrow g` was chosen
-- to have `g` as its underlying morphism.
/-- Reading off the comparison isomorphism of the object built from `g` recovers `g`. -/
private theorem exampleCategoricalPullbackFromArrow_hom
    (g : exampleTwoArrowGroup) :
    (exampleCategoricalPullbackFromArrow g).iso.hom = g := sorry

-- Proof sketch: an object of the categorical pullback over the constant point functor has only
-- the unique left and right objects available, so it is determined entirely by its comparison
-- isomorphism.
/-- Every object of the categorical pullback is recovered from its comparison automorphism. -/
private theorem exampleCategoricalPullback_from_hom
    (P : exampleCategoricalPullback) :
    exampleCategoricalPullbackFromArrow P.iso.hom = P := sorry

/-- The objects of the categorical pullback are in bijection with the two automorphisms of the
unique object of the two-arrow groupoid. -/
private noncomputable def exampleCategoricalPullbackEquivGroup :
    exampleCategoricalPullback ≃ exampleTwoArrowGroup :=
  { toFun := fun P ↦ P.iso.hom
    invFun := exampleCategoricalPullbackFromArrow
    left_inv := exampleCategoricalPullback_from_hom
    right_inv := exampleCategoricalPullbackFromArrow_hom }

-- Proof sketch: the object-reconstruction equivalence identifies the object type of the
-- categorical pullback with the two automorphisms of the unique object of the base groupoid.
/-- The categorical pullback in Example 4.32.4 has finitely many objects. -/
private noncomputable instance :
    Fintype exampleCategoricalPullback :=
  Fintype.ofEquiv exampleTwoArrowGroup exampleCategoricalPullbackEquivGroup.symm

-- Proof sketch: an object of the categorical pullback is determined by the unique left and right
-- objects together with an automorphism of the unique object of the base groupoid, and there are
-- exactly two such automorphisms.
/-- The categorical pullback construction in Example 4.32.4 has exactly two objects. -/
private theorem exampleCategoricalPullback_card_eq_two :
    Fintype.card exampleCategoricalPullback = 2 := sorry

-- Proof sketch: any morphism in the categorical pullback has identity first and second
-- components, so the compatibility condition forces equality of the comparison isomorphisms;
-- the object-reconstruction theorem then identifies the endpoints.
/-- A morphism in the categorical pullback forces its source and target objects to coincide. -/
private theorem exampleCategoricalPullback_eq_of_hom
    {P Q : exampleCategoricalPullback} (f : P ⟶ Q) :
    P = Q := by
  have hf_fst : exampleOnePointToTwoArrowGroupoid.map f.fst = 𝟙 _ :=
    by simp [exampleOnePointToTwoArrowGroupoid]
  have hf_snd : exampleOnePointToTwoArrowGroupoid.map f.snd = 𝟙 _ :=
    by simp [exampleOnePointToTwoArrowGroupoid]
  have hhom :
      P.iso.hom = Q.iso.hom := by
    simpa [hf_fst, hf_snd] using f.w.symm
  calc
    P = exampleCategoricalPullbackFromArrow P.iso.hom := by
      symm
      exact exampleCategoricalPullback_from_hom P
    _ = exampleCategoricalPullbackFromArrow Q.iso.hom := by
      simp [hhom]
    _ = Q := exampleCategoricalPullback_from_hom Q

private instance : IsDiscrete exampleCategoricalPullback where
  subsingleton _ _ := by
    sorry
  eq_of_hom := exampleCategoricalPullback_eq_of_hom

/-- Example 4.32.4 (1): the categorical pullback of the cospan
`exampleOnePointToTwoArrowGroupoid, exampleOnePointToTwoArrowGroupoid` is discrete. -/
instance example_categorical_pullback_isDiscrete :
    IsDiscrete (exampleOnePointToTwoArrowGroupoid ⊡ exampleOnePointToTwoArrowGroupoid) := by
  change IsDiscrete exampleCategoricalPullback
  infer_instance

/-- Example 4.32.4 (2): viewed as an ordinary categorical pullback, the pullback of the one-point
category with itself over the one-object two-arrow groupoid has exactly two objects. -/
theorem example_categorical_pullback_card_eq_two :
    Fintype.card (exampleOnePointToTwoArrowGroupoid ⊡ exampleOnePointToTwoArrowGroupoid) = 2 := by
  simpa using exampleCategoricalPullback_card_eq_two

-- Proof sketch: in the `2`-fibre product over `exampleTwoArrowGroupoid`, the comparison
-- isomorphism lives in the fibre of the identity functor over the unique base object, so it must
-- be the identity; hence the resulting category has a unique object.
private instance : Subsingleton exampleCategoryOverPullback := sorry

/-- The `2`-fibre product in `Cat/exampleTwoArrowGroupoid` has a unique object. -/
private noncomputable instance : Unique exampleCategoryOverPullback :=
  uniqueOfSubsingleton exampleCategoryOverPullbackPoint

/-- The `2`-fibre product in `Cat/exampleTwoArrowGroupoid` has finitely many objects. -/
private noncomputable instance :
    Fintype exampleCategoryOverPullback :=
  inferInstance

/-- Example 4.32.4 (3): in `Cat/exampleTwoArrowGroupoid`, the canonical `2`-fibre product of the
one-point category with itself has a unique object. -/
noncomputable instance example_category_over_pullback_unique :
    Unique
      ((explicitTwoFibreProduct
        exampleOnePointOverGroupoid.toBase
        exampleOnePointOverGroupoid.toBase).obj) := by
  change Unique exampleCategoryOverPullback
  infer_instance

-- Proof sketch: in the pullback over the base groupoid, the comparison isomorphism must lie over
-- the identity of the unique base object, so the only possible comparison arrow is the identity;
-- hence there is only one object.
/-- The pullback construction in `Cat/exampleTwoArrowGroupoid` for Example 4.32.4 has exactly one
object. -/
private theorem exampleCategoryOverPullback_card_eq_one :
    Fintype.card exampleCategoryOverPullback = 1 := sorry

/-- Example 4.32.4 (4): viewed as the canonical `2`-fibre product in `Cat/exampleTwoArrowGroupoid`,
the pullback of the one-point category with itself has exactly one object. -/
theorem example_category_over_pullback_card_eq_one :
    Fintype.card
      ((explicitTwoFibreProduct
        exampleOnePointOverGroupoid.toBase
        exampleOnePointOverGroupoid.toBase).obj) = 1 := by
  simpa only [exampleCategoryOverPullback] using exampleCategoryOverPullback_card_eq_one

-- Proof sketch: the point category is discrete and the only admissible base morphism is the
-- identity, so every morphism in the pullback over the base is forced to be the identity.
private instance : IsDiscrete exampleCategoryOverPullback where
  subsingleton _ _ := by
    sorry
  eq_of_hom := fun {_ _} _ ↦ Subsingleton.elim _ _

/-- Example 4.32.4 (5): in `Cat/exampleTwoArrowGroupoid`, the canonical `2`-fibre product of the
one-point category with itself is discrete. -/
instance example_category_over_pullback_isDiscrete :
    IsDiscrete
      ((explicitTwoFibreProduct
        exampleOnePointOverGroupoid.toBase
        exampleOnePointOverGroupoid.toBase).obj) := by
  change IsDiscrete exampleCategoryOverPullback
  infer_instance

-- Proof sketch: equivalences preserve the cardinality of the object type. The categorical
-- pullback has two objects by `exampleCategoricalPullback_card_eq_two`, while the pullback in
-- `Cat/exampleTwoArrowGroupoid` has one object by `exampleCategoryOverPullback_card_eq_one`.
/-- Example 4.32.4 (6): the `2`-fibre product of the one-point discrete category with itself over the
one-object two-arrow groupoid depends on whether we form it as a pullback of categories or as a
pullback in `Cat/exampleTwoArrowGroupoid`; the two resulting categories are not equivalent. -/
theorem example_two_fibre_product_constructions_not_equivalent :
    ¬ Nonempty
        (exampleOnePointToTwoArrowGroupoid ⊡ exampleOnePointToTwoArrowGroupoid ≌
          (explicitTwoFibreProduct
            exampleOnePointOverGroupoid.toBase
            exampleOnePointOverGroupoid.toBase).obj) := sorry

end CategoryTheory
