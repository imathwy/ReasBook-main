import Mathlib.CategoryTheory.Category.Cat

universe u v

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

/-- Helper for Chap08 Lemma 8 8 1: the object type of a `Cat`-valued presheaf at one base,
lifted to the same universe as the arrow type. -/
abbrev catPresheafObjFiber (F : Cᵒᵖ ⥤ Cat.{v, u}) (U : Cᵒᵖ) : Type (max u v) :=
  ULift.{max u v, u} (F.obj U)

/-- Helper for Chap08 Lemma 8 8 1: the object restriction map of a `Cat`-valued presheaf. -/
def catPresheafObjMap (F : Cᵒᵖ ⥤ Cat.{v, u}) {U V : Cᵒᵖ} (f : U ⟶ V) :
    catPresheafObjFiber F U → catPresheafObjFiber F V :=
  fun X => ULift.up ((F.map f).toFunctor.obj X.down)

/-- Helper for Chap08 Lemma 8 8 1: object restriction is the identity on identity arrows. -/
private theorem catPresheafObjMap_id (F : Cᵒᵖ ⥤ Cat.{v, u}) (U : Cᵒᵖ) :
    catPresheafObjMap F (𝟙 U) = id := by
  -- Reduce to the underlying object of the lifted fiber and use functoriality of `F`.
  funext X
  cases X
  simp [catPresheafObjMap]

/-- Helper for Chap08 Lemma 8 8 1: object restriction respects composition. -/
private theorem catPresheafObjMap_comp (F : Cᵒᵖ ⥤ Cat.{v, u})
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    catPresheafObjMap F (f ≫ g) = (catPresheafObjMap F g) ∘ (catPresheafObjMap F f) := by
  -- Work pointwise; the `Cat` wrapper then reduces to ordinary functor composition.
  funext X
  cases X
  simp [catPresheafObjMap]

/-- Helper for Chap08 Lemma 8 8 1: the object presheaf underlying a `Cat`-valued presheaf. -/
def catPresheafObj (F : Cᵒᵖ ⥤ Cat.{v, u}) : Cᵒᵖ ⥤ Type (max u v) where
  obj U := catPresheafObjFiber F U
  map f := catPresheafObjMap F f
  map_id := catPresheafObjMap_id F
  map_comp := catPresheafObjMap_comp F

/-- Helper for Chap08 Lemma 8 8 1: the arrow type of a `Cat`-valued presheaf at one base. -/
abbrev catPresheafArrFiber (F : Cᵒᵖ ⥤ Cat.{v, u}) (U : Cᵒᵖ) : Type (max u v) :=
  Sigma fun X : (F.obj U : Type u) => Sigma fun Y : (F.obj U : Type u) => X ⟶ Y

/-- Helper for Chap08 Lemma 8 8 1: the arrow restriction map of a `Cat`-valued presheaf. -/
def catPresheafArrMap (F : Cᵒᵖ ⥤ Cat.{v, u}) {U V : Cᵒᵖ} (f : U ⟶ V) :
    catPresheafArrFiber F U → catPresheafArrFiber F V :=
  fun a =>
    ⟨(F.map f).toFunctor.obj a.1,
      ⟨(F.map f).toFunctor.obj a.2.1, (F.map f).toFunctor.map a.2.2⟩⟩

/-- Helper for Chap08 Lemma 8 8 1: arrow restriction is the identity on identity arrows. -/
private theorem catPresheafArrMap_id (F : Cᵒᵖ ⥤ Cat.{v, u}) (U : Cᵒᵖ) :
    catPresheafArrMap F (𝟙 U) = id := by
  -- Expose the wrapped functor equality in `Cat`, then split the dependent arrow package.
  funext a
  have hF :
      (F.map (𝟙 U)).toFunctor = (𝟙 (F.obj U) : F.obj U ⟶ F.obj U).toFunctor :=
    congrArg Cat.Hom.toFunctor (F.map_id U)
  cases a with
  | mk X rest =>
    cases rest with
    | mk Y h =>
      dsimp [catPresheafArrMap]
      rw [hF]
      simp

/-- Helper for Chap08 Lemma 8 8 1: arrow restriction respects composition. -/
private theorem catPresheafArrMap_comp (F : Cᵒᵖ ⥤ Cat.{v, u})
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    catPresheafArrMap F (f ≫ g) = (catPresheafArrMap F g) ∘ (catPresheafArrMap F f) := by
  -- Split the source/target/morphism package, then rewrite the `Cat`-wrapped composition once.
  funext a
  have hF : (F.map (f ≫ g)).toFunctor = ((F.map f) ≫ (F.map g)).toFunctor :=
    congrArg Cat.Hom.toFunctor (F.map_comp f g)
  cases a with
  | mk X rest =>
    cases rest with
    | mk Y h =>
      dsimp [catPresheafArrMap]
      rw [hF]
      rfl

/-- Helper for Chap08 Lemma 8 8 1: the arrow presheaf underlying a `Cat`-valued presheaf. -/
def catPresheafArr (F : Cᵒᵖ ⥤ Cat.{v, u}) : Cᵒᵖ ⥤ Type (max u v) where
  obj U := catPresheafArrFiber F U
  map f := catPresheafArrMap F f
  map_id := catPresheafArrMap_id F
  map_comp := catPresheafArrMap_comp F

/-- Helper for Chap08 Lemma 8 8 1: the type of composable arrow pairs at one base. -/
abbrev catPresheafComposableFiber (F : Cᵒᵖ ⥤ Cat.{v, u}) (U : Cᵒᵖ) :
    Type (max u v) :=
  Sigma fun X : (F.obj U : Type u) =>
    Sigma fun Y : (F.obj U : Type u) =>
      Sigma fun Z : (F.obj U : Type u) => (X ⟶ Y) × (Y ⟶ Z)

/-- Helper for Chap08 Lemma 8 8 1: restriction of composable arrow pairs. -/
def catPresheafComposableMap (F : Cᵒᵖ ⥤ Cat.{v, u}) {U V : Cᵒᵖ} (f : U ⟶ V) :
    catPresheafComposableFiber F U → catPresheafComposableFiber F V :=
  fun a =>
    ⟨(F.map f).toFunctor.obj a.1,
      ⟨(F.map f).toFunctor.obj a.2.1,
        ⟨(F.map f).toFunctor.obj a.2.2.1,
          ((F.map f).toFunctor.map a.2.2.2.1,
            (F.map f).toFunctor.map a.2.2.2.2)⟩⟩⟩

/-- Helper for Chap08 Lemma 8 8 1: composable-pair restriction is identity on identity arrows. -/
private theorem catPresheafComposableMap_id (F : Cᵒᵖ ⥤ Cat.{v, u}) (U : Cᵒᵖ) :
    catPresheafComposableMap F (𝟙 U) = id := by
  -- Use the underlying identity functor, then split the three objects and two arrows.
  funext a
  have hF :
      (F.map (𝟙 U)).toFunctor = (𝟙 (F.obj U) : F.obj U ⟶ F.obj U).toFunctor :=
    congrArg Cat.Hom.toFunctor (F.map_id U)
  cases a with
  | mk X rest =>
    cases rest with
    | mk Y rest =>
      cases rest with
      | mk Z hs =>
        dsimp [catPresheafComposableMap]
        rw [hF]
        simp

/-- Helper for Chap08 Lemma 8 8 1: composable-pair restriction respects composition. -/
private theorem catPresheafComposableMap_comp (F : Cᵒᵖ ⥤ Cat.{v, u})
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    catPresheafComposableMap F (f ≫ g) =
      (catPresheafComposableMap F g) ∘ (catPresheafComposableMap F f) := by
  -- Split the package, then rewrite the single wrapped `Cat` composition.
  funext a
  have hF : (F.map (f ≫ g)).toFunctor = ((F.map f) ≫ (F.map g)).toFunctor :=
    congrArg Cat.Hom.toFunctor (F.map_comp f g)
  cases a with
  | mk X rest =>
    cases rest with
    | mk Y rest =>
      cases rest with
      | mk Z hs =>
        dsimp [catPresheafComposableMap]
        rw [hF]
        rfl

/-- Helper for Chap08 Lemma 8 8 1: the presheaf of composable arrow pairs. -/
def catPresheafComposable (F : Cᵒᵖ ⥤ Cat.{v, u}) : Cᵒᵖ ⥤ Type (max u v) where
  obj U := catPresheafComposableFiber F U
  map f := catPresheafComposableMap F f
  map_id := catPresheafComposableMap_id F
  map_comp := catPresheafComposableMap_comp F

/-- Helper for Chap08 Lemma 8 8 1: the source projection from arrows to objects is natural. -/
private theorem catPresheafSrc_naturality (F : Cᵒᵖ ⥤ Cat.{v, u}) {U V : Cᵒᵖ}
    (f : U ⟶ V) :
    (catPresheafArr F).map f ≫ (fun a => ULift.up a.1) =
      (fun a => ULift.up a.1) ≫ (catPresheafObj F).map f := by
  -- Both sides are the same object restriction after unfolding the arrow map.
  rfl

/-- Helper for Chap08 Lemma 8 8 1: the source projection from arrows to objects. -/
def catPresheafSrc (F : Cᵒᵖ ⥤ Cat.{v, u}) : catPresheafArr F ⟶ catPresheafObj F where
  app _ a := ULift.up a.1
  naturality := fun {_} {_} f => catPresheafSrc_naturality F f

/-- Helper for Chap08 Lemma 8 8 1: the target projection from arrows to objects is natural. -/
private theorem catPresheafTgt_naturality (F : Cᵒᵖ ⥤ Cat.{v, u}) {U V : Cᵒᵖ}
    (f : U ⟶ V) :
    (catPresheafArr F).map f ≫ (fun a => ULift.up a.2.1) =
      (fun a => ULift.up a.2.1) ≫ (catPresheafObj F).map f := by
  -- Both sides are the same target-object restriction after unfolding the arrow map.
  rfl

/-- Helper for Chap08 Lemma 8 8 1: the target projection from arrows to objects. -/
def catPresheafTgt (F : Cᵒᵖ ⥤ Cat.{v, u}) : catPresheafArr F ⟶ catPresheafObj F where
  app _ a := ULift.up a.2.1
  naturality := fun {_} {_} f => catPresheafTgt_naturality F f

/-- Helper for Chap08 Lemma 8 8 1: identity arrows form a natural map from objects to arrows. -/
private theorem catPresheafId_naturality (F : Cᵒᵖ ⥤ Cat.{v, u}) {U V : Cᵒᵖ}
    (f : U ⟶ V) :
    (catPresheafObj F).map f ≫
        (fun X : catPresheafObjFiber F V =>
          (⟨X.down, ⟨X.down, 𝟙 X.down⟩⟩ : catPresheafArrFiber F V)) =
      (fun X : catPresheafObjFiber F U =>
          (⟨X.down, ⟨X.down, 𝟙 X.down⟩⟩ : catPresheafArrFiber F U)) ≫
        (catPresheafArr F).map f := by
  -- Unfold the object and arrow restrictions; functors preserve identity morphisms.
  funext X
  cases X
  dsimp [catPresheafObj, catPresheafObjMap, catPresheafArr, catPresheafArrMap]
  simp

/-- Helper for Chap08 Lemma 8 8 1: the identity-arrow map from objects to arrows. -/
def catPresheafId (F : Cᵒᵖ ⥤ Cat.{v, u}) : catPresheafObj F ⟶ catPresheafArr F where
  app _ X := ⟨X.down, ⟨X.down, 𝟙 X.down⟩⟩
  naturality := fun {_} {_} f => catPresheafId_naturality F f

/-- Helper for Chap08 Lemma 8 8 1: composition of composable arrow pairs is natural. -/
private theorem catPresheafComp_naturality (F : Cᵒᵖ ⥤ Cat.{v, u}) {U V : Cᵒᵖ}
    (f : U ⟶ V) :
    (catPresheafComposable F).map f ≫
        (fun a : catPresheafComposableFiber F V =>
          (⟨a.1, ⟨a.2.2.1, a.2.2.2.1 ≫ a.2.2.2.2⟩⟩ : catPresheafArrFiber F V)) =
      (fun a : catPresheafComposableFiber F U =>
          (⟨a.1, ⟨a.2.2.1, a.2.2.2.1 ≫ a.2.2.2.2⟩⟩ : catPresheafArrFiber F U)) ≫
        (catPresheafArr F).map f := by
  -- Split the composable pair and use preservation of composition by the restriction functor.
  funext a
  cases a with
  | mk X rest =>
    cases rest with
    | mk Y rest =>
      cases rest with
      | mk Z hs =>
        dsimp [catPresheafComposable, catPresheafComposableMap, catPresheafArr,
          catPresheafArrMap]
        simp [Functor.map_comp]

/-- Helper for Chap08 Lemma 8 8 1: the composition map from composable pairs to arrows. -/
def catPresheafComp (F : Cᵒᵖ ⥤ Cat.{v, u}) :
    catPresheafComposable F ⟶ catPresheafArr F where
  app _ a := ⟨a.1, ⟨a.2.2.1, a.2.2.2.1 ≫ a.2.2.2.2⟩⟩
  naturality := fun {_} {_} f => catPresheafComp_naturality F f

end CategoryTheory
