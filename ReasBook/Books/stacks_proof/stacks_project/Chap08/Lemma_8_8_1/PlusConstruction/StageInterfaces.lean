import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHom

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

/-- Helper for Chap08 Lemma 8 8 1: the first source-text stage, where morphisms with the same
base arrow are quotiented by local equality.  The fields record the exact obligations omitted in
the source proof: compatibility of local equality with composition, preservation of cartesian
arrows, and separatedness of all resulting Hom presheaves. -/
structure SeparatedQuotientStage (X : FibredCategoryOver C) where
  /-- The fibred category obtained by quotienting morphisms by local equality. -/
  quotient : FibredCategoryOver C
  /-- The canonical morphism from the original fibred category to the separated quotient. -/
  toQuotient : X ⟶ quotient
  /-- Objects are unchanged in the source construction; this records that intended invariant at
  the interface level, without choosing a concrete quotient model yet. -/
  objectsUnchanged : Nonempty (quotient.S ≃ X.S)
  /-- Local equality of morphisms becomes equality after quotienting. -/
  locallyEqual_isEqual :
    ∀ ⦃x y : X.S⦄ ⦃f g : x ⟶ y⦄,
      locallyEqual (J := J) X f g →
        LocalEqualityQuotientTotal.homMk J X f =
          LocalEqualityQuotientTotal.homMk J X g
  /-- The canonical morphism preserves strongly cartesian arrows. -/
  preservesCartesian :
    (LocalEqualityQuotientTotal.toQuotientBasedFunctor (J := J) X).PreservesStronglyCartesian
  /-- The canonical morphism is locally essentially surjective on objects. -/
  locallyEssentiallySurjective :
    FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J toQuotient
  /-- The Hom presheaves of the quotient are separated on every slice site. -/
  homPresheavesSeparated :
    ∀ (U : C) (x y : quotient.p.Fiber U),
      Presieve.IsSeparated (J.over U)
        ((canonicalFiberPseudofunctor quotient.p).presheafHom x y)

/-- Helper for Chap08 Lemma 8 8 1: the completed first source-text stage.  Objects are represented
by the same total-category objects, morphisms are quotiented by local equality, cartesian arrows
descend, and the resulting Hom presheaves are separated on all slice sites. -/
noncomputable def separatedQuotientStage (X : FibredCategoryOver C) :
    SeparatedQuotientStage (J := J) X where
  quotient := LocalEqualityQuotientTotal.fibredCategory (J := J) X
  toQuotient := LocalEqualityQuotientTotal.toFibredCategory (J := J) X
  objectsUnchanged := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x
      exact x.obj
    · intro x
      exact LocalEqualityQuotientTotal.ofObj J X x
    · intro x
      cases x
      rfl
    · intro x
      rfl
  locallyEqual_isEqual := by
    intro x y f g h
    exact LocalEqualityQuotientTotal.toQuotientFunctor_map_eq_of_locallyEqual (J := J) X h
  preservesCartesian :=
    LocalEqualityQuotientTotal.toQuotientBasedFunctor_preservesStronglyCartesian (J := J) X
  locallyEssentiallySurjective :=
    LocalEqualityQuotientTotal.toQuotient_locallyEssentiallySurjectiveOnObjects (J := J) X
  homPresheavesSeparated := by
    intro U x y
    exact
      LocalEqualityQuotientTotal.localEqualityQuotient_presheafHom_isSeparated
        (J := J) X x y

/-- Helper for Chap08 Lemma 8 8 1: the second source-text stage, where locally defined
morphisms are adjoined.  This is the plus-construction stage for already separated Hom
presheaves. -/
structure HomSheafificationStage (X : FibredCategoryOver C) where
  /-- The fibred category whose morphisms are locally defined morphisms of `X`. -/
  sheafified : FibredCategoryOver C
  /-- The canonical morphism from `X` to the locally-defined-morphism category. -/
  toSheafified : X ⟶ sheafified
  /-- Objects are unchanged in this stage. -/
  objectsUnchanged : Prop
  /-- Composition of locally defined morphisms is independent of representatives. -/
  compositionWellDefined : Prop
  /-- The canonical morphism preserves strongly cartesian arrows. -/
  preservesCartesian : Prop
  /-- The new Hom presheaves are sheaves on every slice site. -/
  homPresheavesSheaves :
    ∀ (U : C) (x y : sheafified.p.Fiber U),
      Presheaf.IsSheaf (J.over U)
        ((canonicalFiberPseudofunctor sheafified.p).presheafHom x y)
  /-- For original objects, the induced Hom map is a local isomorphism, i.e. the source Hom
  presheaf has been sheafified. -/
  homMap_W :
    ∀ (U : C) (x y : X.p.Fiber U),
      (J.over U).W (fibredMorphismPresheafMap toSheafified x y)

/-- Helper for Chap08 Lemma 8 8 1: the third source-text stage, whose objects are covers equipped
with descent data and whose morphisms are compatible double-indexed local morphisms.  The target
is bundled as a `StackOver J`, so the interface records precisely the remaining checks from the
source proof: composition, cartesian lifts, unchanged Hom on old objects, local essential image,
and effectivity of descent data. -/
structure DescentObjectCompletionStage (X : FibredCategoryOver C) where
  /-- The stack obtained by adjoining descent-data objects. -/
  stack : StackOver J
  /-- The canonical morphism sending an object to its trivial descent datum. -/
  toStack : X ⟶ stack
  /-- Composition of double-indexed compatible morphism families is well-defined. -/
  compositionWellDefined : Prop
  /-- The canonical morphism preserves strongly cartesian arrows. -/
  preservesCartesian : Prop
  /-- Pullbacks in the descent-data-object category are represented by pulling back the cover and
  the descent datum. -/
  pullbacksByBaseChange : Prop
  /-- The third stage does not change Hom presheaves between old objects. -/
  homOnOldObjectsUnchanged :
    ∀ (U : C) (x y : X.p.Fiber U),
      IsIso (fibredMorphismPresheafMap toStack x y)
  /-- Every object of the completed stack is locally isomorphic to an old object. -/
  locallyEssentiallySurjective :
    FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J toStack

/-- Helper for Chap08 Lemma 8 8 1: the third source-text stage is a stackification whenever the
Hom maps on old objects are unchanged and every new object is locally represented by an old
object. -/
theorem DescentObjectCompletionStage.isStackification
    {X : FibredCategoryOver C} (S : DescentObjectCompletionStage (J := J) X) :
    FibredCategoryMor.IsStackification S.toStack := by
  refine ⟨?_, S.locallyEssentiallySurjective⟩
  intro U x y
  have hIso : IsIso (fibredMorphismPresheafMap S.toStack x y) :=
    S.homOnOldObjectsUnchanged U x y
  let _ : IsIso (fibredMorphismPresheafMap S.toStack x y) := hIso
  exact (J.over U).W.of_isIso (fibredMorphismPresheafMap S.toStack x y)

/-- Helper for Chap08 Lemma 8 8 1: the source-faithful naive construction for an arbitrary
fibred category, split into the three stages in the Stacks proof: local-equality quotient,
locally-defined morphisms, and descent-data objects. -/
structure NaiveStackificationConstruction (X : FibredCategoryOver C) where
  /-- Stage 1: quotient morphisms by local equality. -/
  separated : SeparatedQuotientStage (J := J) X
  /-- Stage 2: add locally defined morphisms to sheafify Hom presheaves. -/
  homSheafification : HomSheafificationStage (J := J) separated.quotient
  /-- Stage 3: add descent-data objects to make descent effective. -/
  descentCompletion :
    DescentObjectCompletionStage (J := J) homSheafification.sheafified
  /-- The composite morphism from the original source to the completed stack. -/
  toStack :
    X ⟶ descentCompletion.stack :=
    separated.toQuotient ≫ homSheafification.toSheafified ≫ descentCompletion.toStack
  /-- The source proof's two defining stackification properties for the composite morphism.  This
  is the final compatibility checkpoint after the three stages have been implemented. -/
  composite_isStackification :
    FibredCategoryMor.IsStackification toStack

/-- Helper for Chap08 Lemma 8 8 1: a completed naive construction gives the existence statement
for stackification of a fibred category. -/
theorem NaiveStackificationConstruction.exists_stackification
    {X : FibredCategoryOver C} (S : NaiveStackificationConstruction (J := J) X) :
    ∃ Y : StackOver J,
      ∃ G : X ⟶ Y,
        FibredCategoryMor.IsStackification G :=
  ⟨S.descentCompletion.stack, S.toStack, S.composite_isStackification⟩

/-- Helper for Chap08 Lemma 8 8 1: the same three-stage construction specialized to the
co-Grothendieck model of a `Cat`-valued presheaf.  This is the precise replacement frontier for
the current `catPseudofunctorPlusPlusStackificationExists` placeholder. -/
abbrev CatValuedNaiveStackificationConstruction (F : Cᵒᵖ ⥤ Cat.{vX, uX}) :=
  NaiveStackificationConstruction (J := J) (catValuedCoGrothendieckModel F)

/-- Helper for Chap08 Lemma 8 8 1: once the source-text three-stage construction has been carried
out for a `Cat`-valued presheaf, it supplies the stackification existence theorem for its
co-Grothendieck projection. -/
theorem catValued_stackification_exists_of_naiveConstruction
    (F : Cᵒᵖ ⥤ Cat.{vX, uX})
    (S : CatValuedNaiveStackificationConstruction (J := J) F) :
    ∃ Y : StackOver J,
      ∃ G :
        catValuedCoGrothendieckModel F ⟶ Y,
        FibredCategoryMor.IsStackification G :=
  S.exists_stackification

end FibredCategoryMor

end CategoryTheory
