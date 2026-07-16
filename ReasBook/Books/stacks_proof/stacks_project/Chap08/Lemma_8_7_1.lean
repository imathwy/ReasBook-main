import Mathlib
import stacks_proof.stacks_project.Chap04.«4_34_2_1»
import stacks_proof.stacks_project.Chap04.Lemma_4_34_1
import stacks_proof.stacks_project.Chap04.Lemma_4_35_12
import stacks_proof.stacks_project.Chap04.Lemma_4_42_1
import stacks_proof.stacks_project.Chap08.Definition_8_6_1
import stacks_proof.stacks_project.Chap08.Definition_8_6_5
import stacks_proof.stacks_project.Chap08.Definition_8_5_5
import stacks_proof.stacks_project.Chap08.Lemma_8_4_4
import stacks_proof.stacks_project.Chap08.Lemma_8_4_6
import stacks_proof.stacks_project.Chap08.Lemma_8_5_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open Bicategory.InducedBicategory
open Functor Functor.Fiber IsHomLift

attribute [local instance] uliftCategory

variable {C : Type u} [Category.{v} C]

section

variable {J : GrothendieckTopology C}

namespace FibredCategoryOver

  -- Route correction: `FibredCategoryOver.toBase` is universe-restricted, so the absolute branch
  -- uses the universe-polymorphic based functor to the base instead.
/-- Helper for Chap08 Lemma 8 7 1: the raw absolute inertia projection of a fibred category is
again fibred, so it can be repackaged as a fibred category over the base. -/
private instance relativeInertiaProjectionSelf_isFibered (X : FibredCategoryOver C) :
    (relativeInertiaProjection X.p X.p).IsFibered :=
  CategoryOver.relativeInertiaProjection_self_isFibered (p := X.p)

/-- Helper for Chap08 Lemma 8 7 1: the absolute inertia of a fibred category over `C` is the
fibred category associated to its raw self-inertia projection. -/
abbrev absoluteInertiaOver (X : FibredCategoryOver.{u, v, max u v, v} C) :
    FibredCategoryOver C :=
  FibredCategoryOver.ofFunctor (relativeInertiaProjection X.p X.p)

end FibredCategoryOver

-- Proof sketch: this is the exact target of the Chapter 4 equivalence from relative inertia to
-- the diagonal self-`2`-fibre product. The missing ingredient is the earlier pullback-stack
-- closure theorem for this explicit owner.
/-- Helper for Chap08 Lemma 8 7 1: the diagonal self-pullback model of relative inertia is a
stack on the site. -/
private theorem relativeInertiaDiagonalPullback_isStackOnSite
    {X Y : FibredCategoryOver.{u, v, max u v, v} C}
    [IsStackOnSite J X.p] [IsStackOnSite J Y.p] (F : X ⟶ Y) :
    IsStackOnSite J
      (CategoryOver.explicitTwoFibreProduct
        (BasedFunctor.relativeDiagonalOver (FibredCategoryMor.toBasedFunctor F))
        (BasedFunctor.relativeDiagonalOver (FibredCategoryMor.toBasedFunctor F))).p := by
  let Xstack : StackOver J := ⟨X, inferInstance⟩
  let Ystack : StackOver J := ⟨Y, inferInstance⟩
  let Fstack : Xstack ⟶ Ystack := InducedCategory.Hom.ofFibredCategoryMor F
  have hPullback : IsStackOnSite J
      (FibredCategoryOver.twoFibreProduct
        (InducedCategory.Hom.toFibredCategoryMor Fstack)
        (InducedCategory.Hom.toFibredCategoryMor Fstack)).p :=
    stackTwoFibreProduct_isStack (J := J) Fstack Fstack
  let Pstack : StackOver J :=
    ⟨FibredCategoryOver.twoFibreProduct
      (InducedCategory.Hom.toFibredCategoryMor Fstack)
      (InducedCategory.Hom.toFibredCategoryMor Fstack), hPullback⟩
  let diagonal : Xstack.toFibredCategoryOver ⟶ Pstack.toFibredCategoryOver :=
    FibredCategoryMor.ofBasedFunctor
      (BasedFunctor.relativeDiagonalOver (FibredCategoryMor.toBasedFunctor F))
      (relativeDiagonalOver_preserves_strongly_cartesian F)
  let diagonalStack : Xstack ⟶ Pstack :=
    InducedCategory.Hom.ofFibredCategoryMor diagonal
  have hDiagonalPullback : IsStackOnSite J
      (FibredCategoryOver.twoFibreProduct
        (InducedCategory.Hom.toFibredCategoryMor diagonalStack)
        (InducedCategory.Hom.toFibredCategoryMor diagonalStack)).p :=
    stackTwoFibreProduct_isStack (J := J) diagonalStack diagonalStack
  -- The second pullback is definitionally the explicit diagonal self-pullback used by the
  -- Chapter 4 relative-inertia equivalence.
  simpa [Pstack, diagonalStack, diagonal, Fstack, Xstack, Ystack] using hDiagonalPullback

-- Proof sketch: transport the stack structure from the diagonal self-`2`-fibre product along
-- the Chapter 4 equivalence between relative inertia and that pullback.
/-- Helper for Chap08 Lemma 8 7 1: relative inertia preserves the stack-on-site condition. -/
private theorem relativeInertiaOver_isStackOnSite
    {X Y : FibredCategoryOver.{u, v, max u v, v} C}
    [IsStackOnSite J X.p] [IsStackOnSite J Y.p] (F : X ⟶ Y) :
    IsStackOnSite J (FibredCategoryOver.relativeInertiaOver F).p := by
  let BF := FibredCategoryMor.toBasedFunctor F
  have htarget : IsStackOnSite J
      (CategoryOver.explicitTwoFibreProduct
        (BasedFunctor.relativeDiagonalOver BF)
        (BasedFunctor.relativeDiagonalOver BF)).p :=
    relativeInertiaDiagonalPullback_isStackOnSite (J := J) F
  -- The Chapter 4 comparison is an equivalence over the base, so the stack property transports
  -- from the explicit diagonal self-pullback back to relative inertia.
  have htransport :=
    (isStackOnSite_iff_of_equivalence_over_base J
      (relativeInertiaProjection (FibredCategoryMor.toFunctor F) X.p)
      (CategoryOver.explicitTwoFibreProduct
        (BasedFunctor.relativeDiagonalOver BF)
        (BasedFunctor.relativeDiagonalOver BF)).p
      (BasedFunctor.relativeInertiaToDiagonalPullback BF)
      (BasedFunctor.relativeInertiaEquivalenceOverBase BF)).2 htarget
  simpa [FibredCategoryOver.relativeInertiaOver, BF] using htransport

/-- Helper for Chap08 Lemma 8 7 1: the universe-polymorphic based functor from a fibred category to
the base fibred category preserves strongly cartesian morphisms. -/
private theorem toBaseBasedFunctor_preservesStronglyCartesian
    (X : FibredCategoryOver C) :
    BasedFunctor.PreservesStronglyCartesian X.toBasedCategory.toBase := by
  intro a b φ hφ
  -- The target projection is the identity functor on the base, where every morphism is strongly
  -- cartesian by the existing fibred-in-groupoids instance.
  simpa [BasedCategory.toBase] using
    (inferInstance : IsFibredInGroupoids (𝟭 C)).isStronglyCartesian_map (X.p.map φ)

/-- Helper for Chap08 Lemma 8 7 1: every two objects in a fiber of the identity projection over
the same base object are equal. -/
private theorem identityFiberObj_eq {U : C} (X Y : (𝟭 C).Fiber U) : X = Y := by
  apply Subtype.ext
  exact X.2.trans Y.2.symm

/-- Helper for Chap08 Lemma 8 7 1: every two morphisms in a fiber of the identity projection are
equal. -/
private theorem identityFiberHom_eq {U : C} {X Y : (𝟭 C).Fiber U} (f g : X ⟶ Y) :
    f = g := by
  apply Functor.Fiber.hom_ext
  change f.1 = g.1
  letI : (𝟭 C).IsHomLift (𝟙 U) f.1 := f.2
  letI : (𝟭 C).IsHomLift (𝟙 U) g.1 := g.2
  have hf : (𝟭 C).map f.1 =
      eqToHom (domain_eq (𝟭 C) (𝟙 U) f.1) ≫
        𝟙 U ≫ eqToHom (codomain_eq (𝟭 C) (𝟙 U) f.1).symm := by
    exact fac' (𝟭 C) (𝟙 U) f.1
  have hg : (𝟭 C).map g.1 =
      eqToHom (domain_eq (𝟭 C) (𝟙 U) g.1) ≫
        𝟙 U ≫ eqToHom (codomain_eq (𝟭 C) (𝟙 U) g.1).symm := by
    exact fac' (𝟭 C) (𝟙 U) g.1
  simpa using hf.trans hg.symm

/-- Helper for Chap08 Lemma 8 7 1: fibers of the identity projection are contractible
categories. -/
private abbrev identityFiberIso {U : C} (X Y : (𝟭 C).Fiber U) : X ≅ Y :=
  eqToIso (identityFiberObj_eq X Y)

/-- Helper for Chap08 Lemma 8 7 1: fixed-cover descent for the identity projection is an
equivalence. -/
private theorem identityFunctor_descentData_isEquivalence
    {ι : Type*} {U : C} {Xc : ι → C} (f : ∀ i, Xc i ⟶ U) :
    ((canonicalFiberPseudofunctor (𝟭 C)).toDescentData f).IsEquivalence := by
  let F := (canonicalFiberPseudofunctor (𝟭 C)).toDescentData f
  letI : F.Faithful := by
    constructor
    intro M N φ ψ h
    exact identityFiberHom_eq φ ψ
  letI : F.Full := by
    constructor
    intro M N η
    refine ⟨(identityFiberIso M N).hom, ?_⟩
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    exact identityFiberHom_eq _ _
  letI : F.EssSurj := by
    constructor
    intro D
    let M : (canonicalFiberPseudofunctor (𝟭 C)).obj (.mk (Opposite.op U)) :=
      ⟨U, rfl⟩
    refine ⟨M, ⟨?_⟩⟩
    refine Pseudofunctor.DescentData.isoMk (fun i ↦ ?_) ?_
    · exact identityFiberIso _ _
    · intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
      exact identityFiberHom_eq _ _
  exact Functor.IsEquivalence.mk (F := F) inferInstance inferInstance inferInstance

/-- Helper for Chap08 Lemma 8 7 1: the identity projection of the base category is a stack over
any site on the base. -/
private theorem identityFunctor_isStackOnSite : IsStackOnSite J (𝟭 C) := by
  refine (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J (𝟭 C)).2 ?_
  intro U S
  exact identityFunctor_descentData_isEquivalence (fun I : S.Arrow ↦ I.f)

/-- Helper for Chap08 Lemma 8 7 1: the lifted base projection is the identity projection viewed
in the owner universe used for stacks over `C`. -/
private abbrev uliftBaseProjection : ULift.{max u v, u} C ⥤ C :=
  ULift.downFunctor

/-- Helper for Chap08 Lemma 8 7 1: the lifted base projection composed with `ULift.upFunctor`
is the identity projection on `C`. -/
private theorem upFunctor_comp_uliftBaseProjection :
    ULift.upFunctor ⋙ (uliftBaseProjection (C := C)) = 𝟭 C :=
  rfl

/-- Helper for Chap08 Lemma 8 7 1: the lifted base projection is unchanged after composing with
the identity projection on `C`. -/
private theorem uliftBaseProjection_comp_id :
    (uliftBaseProjection (C := C)) ⋙ 𝟭 C = uliftBaseProjection (C := C) :=
  rfl

/-- Helper for Chap08 Lemma 8 7 1: the base identity maps to its lifted owner model over `C`. -/
private abbrev baseToULiftBase : BasedCategory.ofFunctor (𝟭 C) ⥤ᵇ
    BasedCategory.ofFunctor (uliftBaseProjection (C := C)) where
  toFunctor := ULift.upFunctor
  w := upFunctor_comp_uliftBaseProjection

/-- Helper for Chap08 Lemma 8 7 1: the lifted base owner model maps back to the base identity. -/
private abbrev uliftBaseToBase : BasedCategory.ofFunctor (uliftBaseProjection (C := C)) ⥤ᵇ
    BasedCategory.ofFunctor (𝟭 C) where
  toFunctor := uliftBaseProjection (C := C)
  w := uliftBaseProjection_comp_id

/-- Helper for Chap08 Lemma 8 7 1: the lifted base owner model is equivalent over the base to
the identity projection. -/
private theorem baseToULiftBase_isEquivalenceOverBase :
    (baseToULiftBase (C := C)).IsEquivalenceOverBase := by
  refine BasedFunctor.IsEquivalenceOverBase.mkPrime (uliftBaseToBase (C := C)) ?_ ?_
  · refine BasedNatIso.mkNatIso ?_ ?_
    · exact (ULift.equivalence : C ≌ ULift.{max u v, u} C).unitIso
    · intro a
      simpa [baseToULiftBase, uliftBaseToBase, BasedCategory.ofFunctor] using
        (IsHomLift.id (p := 𝟭 C) rfl : (𝟭 C).IsHomLift (𝟙 a) (𝟙 a))
  · refine BasedNatIso.mkNatIso ?_ ?_
    · exact (ULift.equivalence : C ≌ ULift.{max u v, u} C).counitIso
    · intro a
      simpa [baseToULiftBase, uliftBaseToBase, uliftBaseProjection, BasedCategory.ofFunctor,
        ULift.upFunctor, ULift.downFunctor] using
        (IsHomLift.id (p := uliftBaseProjection (C := C)) rfl :
          (uliftBaseProjection (C := C)).IsHomLift (𝟙 a.down) (𝟙 a.down))

/-- Helper for Chap08 Lemma 8 7 1: the lifted base projection is a stack over the site. -/
private theorem uliftBaseProjection_isStackOnSite :
    IsStackOnSite J (uliftBaseProjection (C := C)) := by
  exact
    (isStackOnSite_iff_of_equivalence_over_base J (𝟭 C)
      (uliftBaseProjection (C := C)) (baseToULiftBase (C := C))
      baseToULiftBase_isEquivalenceOverBase).1 identityFunctor_isStackOnSite

/-- Helper for Chap08 Lemma 8 7 1: the universe-lifted inclusion of the base category. -/
private abbrev baseULiftUpFunctor : C ⥤ ULift.{max u v, u} C :=
  ULift.upFunctor

/-- Helper for Chap08 Lemma 8 7 1: compose a projection with the universe-lifted base
inclusion. -/
private abbrev projectionToULiftBase
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C) :
    S ⥤ ULift.{max u v, u} C :=
  p ⋙ baseULiftUpFunctor

/-- Helper for Chap08 Lemma 8 7 1: an absolute-inertia object also satisfies the lifted-base
identity condition. -/
private theorem relativeInertiaBaseLiftUp_map_hom_eq_id
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject p) :
    (projectionToULiftBase p).map X.α.hom =
      𝟙 ((projectionToULiftBase p).obj X.x) := by
  simpa [projectionToULiftBase, baseULiftUpFunctor, Functor.comp_map, Functor.comp_obj,
    ULift.upFunctor] using X.map_hom_eq_id

/-- Helper for Chap08 Lemma 8 7 1: a lifted-base inertia object also satisfies the ordinary
absolute-inertia identity condition. -/
private theorem relativeInertiaBaseLiftDown_map_hom_eq_id
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject (projectionToULiftBase p)) :
    p.map X.α.hom = 𝟙 (p.obj X.x) := by
  simpa [projectionToULiftBase, baseULiftUpFunctor, Functor.comp_map, Functor.comp_obj,
    ULift.upFunctor] using X.map_hom_eq_id

/-- Helper for Chap08 Lemma 8 7 1: send an absolute-inertia object to the corresponding
lifted-base relative-inertia object. -/
private abbrev relativeInertiaBaseLiftUpObj
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject p) :
    RelativeInertiaObject (projectionToULiftBase p) where
  x := X.x
  α := X.α
  map_hom_eq_id := relativeInertiaBaseLiftUp_map_hom_eq_id p X

/-- Helper for Chap08 Lemma 8 7 1: forget the lifted-base proof condition on an inertia object. -/
private abbrev relativeInertiaBaseLiftDownObj
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject (projectionToULiftBase p)) :
    RelativeInertiaObject p where
  x := X.x
  α := X.α
  map_hom_eq_id := relativeInertiaBaseLiftDown_map_hom_eq_id p X

/-- Helper for Chap08 Lemma 8 7 1: morphisms of absolute-inertia objects are unchanged after
lifting the base identity condition. -/
private abbrev relativeInertiaBaseLiftUpHom
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    {X Y : RelativeInertiaObject p} (φ : X ⟶ Y) :
    relativeInertiaBaseLiftUpObj p X ⟶ relativeInertiaBaseLiftUpObj p Y where
  φ := φ.φ
  comm := φ.comm

/-- Helper for Chap08 Lemma 8 7 1: morphisms of lifted-base inertia objects are unchanged after
forgetting the lifted proof condition. -/
private abbrev relativeInertiaBaseLiftDownHom
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    {X Y : RelativeInertiaObject (projectionToULiftBase p)} (φ : X ⟶ Y) :
    relativeInertiaBaseLiftDownObj p X ⟶ relativeInertiaBaseLiftDownObj p Y where
  φ := φ.φ
  comm := φ.comm

/-- Helper for Chap08 Lemma 8 7 1: the lifted-base inertia functor preserves identities. -/
private theorem relativeInertiaBaseLiftUpHom_id
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject p) :
    relativeInertiaBaseLiftUpHom p (𝟙 X) =
      𝟙 (relativeInertiaBaseLiftUpObj p X) := by
  apply RelativeInertiaHom.ext
  rfl

/-- Helper for Chap08 Lemma 8 7 1: the lifted-base inertia functor preserves composition. -/
private theorem relativeInertiaBaseLiftUpHom_comp
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    {X Y Z : RelativeInertiaObject p} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    relativeInertiaBaseLiftUpHom p (φ ≫ ψ) =
      relativeInertiaBaseLiftUpHom p φ ≫ relativeInertiaBaseLiftUpHom p ψ := by
  apply RelativeInertiaHom.ext
  rfl

/-- Helper for Chap08 Lemma 8 7 1: the lifted-base proof-forgetting functor preserves
identities. -/
private theorem relativeInertiaBaseLiftDownHom_id
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject (projectionToULiftBase p)) :
    relativeInertiaBaseLiftDownHom p (𝟙 X) =
      𝟙 (relativeInertiaBaseLiftDownObj p X) := by
  apply RelativeInertiaHom.ext
  rfl

/-- Helper for Chap08 Lemma 8 7 1: the lifted-base proof-forgetting functor preserves
composition. -/
private theorem relativeInertiaBaseLiftDownHom_comp
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    {X Y Z : RelativeInertiaObject (projectionToULiftBase p)} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    relativeInertiaBaseLiftDownHom p (φ ≫ ψ) =
      relativeInertiaBaseLiftDownHom p φ ≫ relativeInertiaBaseLiftDownHom p ψ := by
  apply RelativeInertiaHom.ext
  rfl

/-- Helper for Chap08 Lemma 8 7 1: the functor from absolute inertia to lifted-base inertia. -/
private abbrev relativeInertiaBaseLiftUpFunctor
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C) :
    RelativeInertiaObject p ⥤ RelativeInertiaObject (projectionToULiftBase p) where
  obj := relativeInertiaBaseLiftUpObj p
  map := relativeInertiaBaseLiftUpHom p
  map_id := relativeInertiaBaseLiftUpHom_id p
  map_comp := relativeInertiaBaseLiftUpHom_comp p

/-- Helper for Chap08 Lemma 8 7 1: the functor from lifted-base inertia back to absolute
inertia. -/
private abbrev relativeInertiaBaseLiftDownFunctor
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C) :
    RelativeInertiaObject (projectionToULiftBase p) ⥤ RelativeInertiaObject p where
  obj := relativeInertiaBaseLiftDownObj p
  map := relativeInertiaBaseLiftDownHom p
  map_id := relativeInertiaBaseLiftDownHom_id p
  map_comp := relativeInertiaBaseLiftDownHom_comp p

/-- Helper for Chap08 Lemma 8 7 1: the lifted-base inertia functor lies over the same base
projection. -/
private theorem relativeInertiaBaseLiftUpFunctor_w
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C) :
    relativeInertiaBaseLiftUpFunctor p ⋙ relativeInertiaProjection (projectionToULiftBase p) p =
      relativeInertiaProjection p p :=
  rfl

/-- Helper for Chap08 Lemma 8 7 1: the lifted-base proof-forgetting functor lies over the same
base projection. -/
private theorem relativeInertiaBaseLiftDownFunctor_w
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C) :
    relativeInertiaBaseLiftDownFunctor p ⋙ relativeInertiaProjection p p =
      relativeInertiaProjection (projectionToULiftBase p) p :=
  rfl

/-- Helper for Chap08 Lemma 8 7 1: the based functor from absolute inertia to lifted-base
inertia. -/
private abbrev relativeInertiaBaseLiftUpBased
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C) :
    BasedCategory.ofFunctor (relativeInertiaProjection p p) ⥤ᵇ
      BasedCategory.ofFunctor (relativeInertiaProjection (projectionToULiftBase p) p) where
  toFunctor := relativeInertiaBaseLiftUpFunctor p
  w := relativeInertiaBaseLiftUpFunctor_w p

/-- Helper for Chap08 Lemma 8 7 1: the based functor from lifted-base inertia to absolute
inertia. -/
private abbrev relativeInertiaBaseLiftDownBased
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C) :
    BasedCategory.ofFunctor (relativeInertiaProjection (projectionToULiftBase p) p) ⥤ᵇ
      BasedCategory.ofFunctor (relativeInertiaProjection p p) where
  toFunctor := relativeInertiaBaseLiftDownFunctor p
  w := relativeInertiaBaseLiftDownFunctor_w p

/-- Helper for Chap08 Lemma 8 7 1: forgetting after lifting gives the original inertia object. -/
private theorem relativeInertiaBaseLiftDownUpObj_eq
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject p) :
    relativeInertiaBaseLiftDownObj p (relativeInertiaBaseLiftUpObj p X) = X := by
  cases X
  simp [relativeInertiaBaseLiftUpObj, relativeInertiaBaseLiftDownObj]

/-- Helper for Chap08 Lemma 8 7 1: lifting after forgetting gives the lifted-base inertia
object. -/
private theorem relativeInertiaBaseLiftUpDownObj_eq
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject (projectionToULiftBase p)) :
    relativeInertiaBaseLiftUpObj p (relativeInertiaBaseLiftDownObj p X) = X := by
  cases X
  simp [relativeInertiaBaseLiftUpObj, relativeInertiaBaseLiftDownObj]

/-- Helper for Chap08 Lemma 8 7 1: the unit comparison has identity underlying inertia
morphism. -/
private theorem relativeInertiaBaseLiftDownUp_eqToHom_hom
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject p) :
    (eqToHom (relativeInertiaBaseLiftDownUpObj_eq p X).symm :
      X ⟶ relativeInertiaBaseLiftDownObj p (relativeInertiaBaseLiftUpObj p X)).φ = 𝟙 X.x := by
  cases X
  rfl

/-- Helper for Chap08 Lemma 8 7 1: the counit comparison has identity underlying inertia
morphism. -/
private theorem relativeInertiaBaseLiftUpDown_eqToHom_hom
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject (projectionToULiftBase p)) :
    (eqToHom (relativeInertiaBaseLiftUpDownObj_eq p X) :
      relativeInertiaBaseLiftUpObj p (relativeInertiaBaseLiftDownObj p X) ⟶ X).φ = 𝟙 X.x := by
  cases X
  rfl

/-- Helper for Chap08 Lemma 8 7 1: the unit component for the lifted-base inertia equivalence
lies over the identity. -/
private theorem relativeInertiaBaseLift_unit_isHomLift
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject p) :
    (relativeInertiaProjection p p).IsHomLift (𝟙 ((relativeInertiaProjection p p).obj X))
      (eqToHom (relativeInertiaBaseLiftDownUpObj_eq p X).symm) := by
  simpa [relativeInertiaProjection, relativeInertiaBaseLiftDownUpObj_eq]
    using
      (IsHomLift.id (p := relativeInertiaProjection p p) rfl :
        (relativeInertiaProjection p p).IsHomLift
          (𝟙 ((relativeInertiaProjection p p).obj X)) (𝟙 X))

/-- Helper for Chap08 Lemma 8 7 1: the counit component for the lifted-base inertia equivalence
lies over the identity. -/
private theorem relativeInertiaBaseLift_counit_isHomLift
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C)
    (X : RelativeInertiaObject (projectionToULiftBase p)) :
    (relativeInertiaProjection (projectionToULiftBase p) p).IsHomLift
      (𝟙 ((relativeInertiaProjection (projectionToULiftBase p) p).obj X))
      (eqToHom (relativeInertiaBaseLiftUpDownObj_eq p X)) := by
  simpa [relativeInertiaProjection, relativeInertiaBaseLiftUpDownObj_eq]
    using
      (IsHomLift.id (p := relativeInertiaProjection (projectionToULiftBase p) p) rfl :
        (relativeInertiaProjection (projectionToULiftBase p) p).IsHomLift
          (𝟙 ((relativeInertiaProjection (projectionToULiftBase p) p).obj X)) (𝟙 X))

/-- Helper for Chap08 Lemma 8 7 1: absolute inertia and lifted-base inertia are equivalent over
the base. -/
private theorem relativeInertiaBaseLiftUpBased_isEquivalenceOverBase
    {S : Type (max u v)} [Category.{v} S] (p : S ⥤ C) :
    (relativeInertiaBaseLiftUpBased p).IsEquivalenceOverBase := by
  refine BasedFunctor.IsEquivalenceOverBase.mkPrime (relativeInertiaBaseLiftDownBased p) ?_ ?_
  · refine BasedNatIso.mkNatIso ?_ ?_
    · refine NatIso.ofComponents (fun X ↦ eqToIso (relativeInertiaBaseLiftDownUpObj_eq p X).symm) ?_
      intro X Y φ
      apply RelativeInertiaHom.ext
      -- Naturality is ordinary identity cancellation on the underlying inertia morphism.
      change φ.φ ≫ 𝟙 Y.x = 𝟙 X.x ≫ φ.φ
      simp
    · intro X
      exact relativeInertiaBaseLift_unit_isHomLift p X
  · refine BasedNatIso.mkNatIso ?_ ?_
    · refine NatIso.ofComponents (fun X ↦ eqToIso (relativeInertiaBaseLiftUpDownObj_eq p X)) ?_
      intro X Y φ
      apply RelativeInertiaHom.ext
      -- The counit naturality check is the same identity cancellation after forgetting proofs.
      change φ.φ ≫ 𝟙 Y.x = 𝟙 X.x ≫ φ.φ
      simp
    · intro X
      exact relativeInertiaBaseLift_counit_isHomLift p X

/-- Helper for Chap08 Lemma 8 7 1: morphisms in the lifted base projection are strongly
cartesian over their image. -/
private theorem uliftBaseProjection_isStronglyCartesian
    {R T : ULift.{max u v, u} C} (f : R ⟶ T) :
    (uliftBaseProjection (C := C)).IsStronglyCartesian
      ((uliftBaseProjection (C := C)).map f) f := by
  cases R with
  | up R =>
    cases T with
    | up T =>
      -- After splitting the `ULift` objects, the lifted projection is the identity projection on
      -- the underlying base morphism.
      refine { toIsHomLift := ?_, universal_property' := ?_ }
      · infer_instance
      · intro a' g ψ hψ
        cases a' with
        | up A =>
          let γ : (ULift.up A : ULift.{max u v, u} C) ⟶ ULift.up R := g
          have hg : (uliftBaseProjection (C := C)).IsHomLift g γ := by
            refine IsHomLift.of_fac (uliftBaseProjection (C := C)) g γ rfl rfl ?_
            simp [γ, ULift.downFunctor]
          refine ⟨γ, ?_, ?_⟩
          · constructor
            · exact hg
            · have hψeq :=
                @IsHomLift.eq_of_isHomLift _ _ _ _ (uliftBaseProjection (C := C)) _ _
                  (g ≫ (uliftBaseProjection (C := C)).map f) ψ hψ
              simpa [γ, uliftBaseProjection, ULift.downFunctor] using hψeq
          · intro χ hχ
            have hχeq :=
              @IsHomLift.eq_of_isHomLift _ _ _ _ (uliftBaseProjection (C := C)) _ _ g χ hχ.1
            simpa [γ, uliftBaseProjection, ULift.downFunctor] using hχeq.symm

/-- Helper for Chap08 Lemma 8 7 1: the lifted structure morphism from a fibred category to the
base preserves strongly cartesian morphisms. -/
private theorem toULiftBase_preservesStronglyCartesian
    (X : FibredCategoryOver.{u, v, max u v, v} C) :
    BasedFunctor.PreservesStronglyCartesian
      (BasedFunctor.comp X.toBasedCategory.toBase (baseToULiftBase (C := C))) := by
  intro a b φ hφ
  simpa [BasedCategory.toBase, baseToULiftBase, uliftBaseProjection] using
    uliftBaseProjection_isStronglyCartesian (C := C) (X.p.map φ)

-- Proof sketch: the raw absolute self-inertia case is the relative-inertia theorem specialized to
-- the universe-polymorphic based functor from `X` to the base fibred category.
/-- Helper for Chap08 Lemma 8 7 1: the raw self-inertia projection of a stack is again a stack
on the site. -/
private theorem relativeInertiaProjectionSelf_isStackOnSite
    (X : FibredCategoryOver.{u, v, max u v, v} C) [IsStackOnSite J X.p] :
    IsStackOnSite J (relativeInertiaProjection X.p X.p) := by
  letI : (uliftBaseProjection (C := C)).IsFibered :=
    (uliftBaseProjection_isStackOnSite (J := J) (C := C)).toIsFibered
  letI : IsStackOnSite J
      (FibredCategoryOver.ofFunctor
        (uliftBaseProjection (C := C)) :
          FibredCategoryOver.{u, v, max u v, v} C).p := by
    simpa [FibredCategoryOver.p, FibredCategoryOver.ofFunctor] using
      (uliftBaseProjection_isStackOnSite (J := J) (C := C))
  let F : X ⟶
      (FibredCategoryOver.ofFunctor
        (uliftBaseProjection (C := C)) :
          FibredCategoryOver.{u, v, max u v, v} C) :=
    FibredCategoryMor.ofBasedFunctor
      (BasedFunctor.comp X.toBasedCategory.toBase (baseToULiftBase (C := C)))
      (toULiftBase_preservesStronglyCartesian X)
  have h : IsStackOnSite J (FibredCategoryOver.relativeInertiaOver F).p :=
    relativeInertiaOver_isStackOnSite (J := J) F
  -- Specializing relative inertia to the canonical map `X → C` is the raw self-inertia
  -- projection used for absolute inertia, after transporting across the lifted-base proof
  -- condition.
  have hLift : IsStackOnSite J (relativeInertiaProjection (projectionToULiftBase X.p) X.p) := by
    simpa [FibredCategoryOver.relativeInertiaOver, F, FibredCategoryMor.toFunctor,
      FibredCategoryMor.toBasedFunctor, FibredCategoryMor.ofBasedFunctor, BasedFunctor.comp,
      BasedCategory.toBase, baseToULiftBase, uliftBaseProjection] using h
  exact
    (isStackOnSite_iff_of_equivalence_over_base J
      (relativeInertiaProjection X.p X.p)
      (relativeInertiaProjection (projectionToULiftBase X.p) X.p)
      (relativeInertiaBaseLiftUpBased X.p)
      (relativeInertiaBaseLiftUpBased_isEquivalenceOverBase X.p)).2 hLift

-- Proof sketch: the absolute stack statement is the raw self-inertia analogue of the relative
-- stack statement above.
/-- Helper for Chap08 Lemma 8 7 1: absolute inertia preserves the stack-on-site condition. -/
private theorem absoluteInertiaOver_isStackOnSite_aux
    (X : FibredCategoryOver C) [IsStackOnSite J X.p] :
    IsStackOnSite J (FibredCategoryOver.absoluteInertiaOver X).p := by
  -- The local owner for absolute inertia is exactly the fibred category associated to raw
  -- self-inertia, so the isolated raw stack helper closes this packaging step.
  simpa [FibredCategoryOver.absoluteInertiaOver] using
    relativeInertiaProjectionSelf_isStackOnSite (J := J) X

-- Proof sketch: a morphism in a relative-inertia fiber is vertical after forgetting to the source
-- fibred category.
/-- Helper for Chap08 Lemma 8 7 1: the underlying source morphism of a relative-inertia fiber
hom lies over the identity of the same base object. -/
private theorem relativeInertiaFiberHom_underlying_isHomLift
    {X Y : FibredCategoryOver.{u, v, max u v, v} C} (F : X ⟶ Y) {U : C}
    {A B : (relativeInertiaProjection (FibredCategoryMor.toFunctor F) X.p).Fiber U}
    (φ : A ⟶ B) :
    X.p.IsHomLift (𝟙 U) φ.1.φ := by
  let q := relativeInertiaProjection (FibredCategoryMor.toFunctor F) X.p
  letI : q.IsHomLift (𝟙 U) φ.1 := φ.2
  -- Project the fiber lift for the inertia projection to the underlying source projection.
  refine of_fac' X.p (𝟙 U) φ.1.φ ?_ ?_ ?_
  · simpa [q, relativeInertiaProjection] using domain_eq q (𝟙 U) φ.1
  · simpa [q, relativeInertiaProjection] using codomain_eq q (𝟙 U) φ.1
  · simpa [q, relativeInertiaProjection] using fac' q (𝟙 U) φ.1

-- Proof sketch: in a source fibred in groupoids, the forgotten vertical morphism is invertible;
-- the relative-inertia extensionality theorem then lifts the inverse back to the fiber.
/-- Helper for Chap08 Lemma 8 7 1: relative-inertia fibers are groupoids when the source fibers
are groupoids. -/
private theorem relativeInertiaProjection_fiber_hom_isIso_of_source
    {X Y : FibredCategoryOver.{u, v, max u v, v} C}
    [IsFibredInGroupoids X.p] (F : X ⟶ Y)
    (U : C)
    {A B : (relativeInertiaProjection (FibredCategoryMor.toFunctor F) X.p).Fiber U}
    (φ : A ⟶ B) :
    IsIso φ := by
  let q := relativeInertiaProjection (FibredCategoryMor.toFunctor F) X.p
  letI : q.IsHomLift (𝟙 U) φ.1 := φ.2
  letI : X.p.IsHomLift (𝟙 U) φ.1.φ :=
    relativeInertiaFiberHom_underlying_isHomLift (F := F) φ
  letI : IsIso (homMk X.p U φ.1.φ) :=
    IsFibredInGroupoids.hom_isIso U (homMk X.p U φ.1.φ)
  letI : IsIso φ.1.φ := by
    simpa using
      (inferInstance :
        IsIso ((fiberInclusion : X.p.Fiber U ⥤ _).map (homMk X.p U φ.1.φ)))
  letI : IsIso φ.1 := RelativeInertiaHom.isIso_of_isIso φ.1
  letI : q.IsHomLift (𝟙 U) (inv φ.1) := by
    simpa [q] using lift_id_inv_isIso q U φ.1
  -- Package the inverse in the standard fiber of the inertia projection.
  refine ⟨?_⟩
  use ⟨inv φ.1, inferInstance⟩
  constructor
  · apply Functor.Fiber.hom_ext
    change φ.1 ≫ inv φ.1 = 𝟙 A.1
    simp
  · apply Functor.Fiber.hom_ext
    change inv φ.1 ≫ φ.1 = 𝟙 B.1
    simp

/-- Helper for Chap08 Lemma 8 7 1: each relative-inertia fiber is a groupoid when the source
projection is fibred in groupoids. -/
private theorem relativeInertiaProjection_fiber_isGroupoid_of_source
    {X Y : FibredCategoryOver.{u, v, max u v, v} C}
    [IsFibredInGroupoids X.p] (F : X ⟶ Y) (U : C) :
    IsGroupoid ((relativeInertiaProjection (FibredCategoryMor.toFunctor F) X.p).Fiber U) where
  all_isIso := relativeInertiaProjection_fiber_hom_isIso_of_source (F := F) U

/-- Helper for Chap08 Lemma 8 7 1: the relative-inertia projection is fibred in groupoids when
the source projection is. -/
private theorem relativeInertiaProjection_isFibredInGroupoids_of_source
    {X Y : FibredCategoryOver.{u, v, max u v, v} C}
    [IsFibredInGroupoids X.p] (F : X ⟶ Y) :
    IsFibredInGroupoids (relativeInertiaProjection (FibredCategoryMor.toFunctor F) X.p) := by
  -- Combine the already available fibredness of relative inertia with the fiberwise groupoid
  -- result above.
  refine
    isFibredInGroupoids_of_isFibered_and_fiber_groupoid
      (relativeInertiaProjection (FibredCategoryMor.toFunctor F) X.p)
      ?_
      ?_
  · infer_instance
  · intro U
    exact relativeInertiaProjection_fiber_isGroupoid_of_source (F := F) U

-- Proof sketch: the absolute self-inertia owner is the same relative-inertia projection with the
-- source projection used on both sides, so the existing Chapter 4 groupoid inheritance applies.
/-- Helper for Chap08 Lemma 8 7 1: raw absolute self-inertia is fibred in groupoids whenever the
source projection is. -/
private theorem relativeInertiaProjectionSelf_isFibredInGroupoids_of_source
    (X : FibredCategoryOver C) [IsFibredInGroupoids X.p] :
    IsFibredInGroupoids (relativeInertiaProjection X.p X.p) := by
  -- Use the public raw self-inertia groupoid theorem and name the specialization for the absolute
  -- branch so later setoid and stack-in-groupoids assembly does not repeat the projection shape.
  exact relativeInertiaProjection_isFibredInGroupoids X.p

-- Proof sketch: thinness of source fibers identifies the forgotten source morphisms; relative
-- inertia and fiber extensionality then identify the original fiber morphisms.
/-- Helper for Chap08 Lemma 8 7 1: relative-inertia fibers are thin when source fibers are
thin. -/
private theorem relativeInertiaProjection_fiber_isThin_of_source
    {X Y : FibredCategoryOver.{u, v, max u v, v} C}
    [IsFibredInSetoids X.p] (F : X ⟶ Y) (U : C) :
    Quiver.IsThin ((relativeInertiaProjection (FibredCategoryMor.toFunctor F) X.p).Fiber U) := by
  intro A B
  refine ⟨?_⟩
  intro φ ψ
  -- Forget both morphisms to the thin source fiber over `U`.
  apply Functor.Fiber.hom_ext
  apply RelativeInertiaHom.ext
  letI : X.p.IsHomLift (𝟙 U) φ.1.φ :=
    relativeInertiaFiberHom_underlying_isHomLift (F := F) φ
  letI : X.p.IsHomLift (𝟙 U) ψ.1.φ :=
    relativeInertiaFiberHom_underlying_isHomLift (F := F) ψ
  have h :
      homMk X.p U φ.1.φ = homMk X.p U ψ.1.φ := by
    exact Subsingleton.elim _ _
  exact congrArg (fun η => η.1) h

/-- Helper for Chap08 Lemma 8 7 1: the relative-inertia projection is fibred in setoids when
the source projection is. -/
private theorem relativeInertiaProjection_isFibredInSetoids_of_source
    {X Y : FibredCategoryOver.{u, v, max u v, v} C}
    [IsFibredInSetoids X.p] (F : X ⟶ Y) :
    IsFibredInSetoids (relativeInertiaProjection (FibredCategoryMor.toFunctor F) X.p) := by
  letI : IsFibredInGroupoids
      (relativeInertiaProjection (FibredCategoryMor.toFunctor F) X.p) :=
    relativeInertiaProjection_isFibredInGroupoids_of_source (F := F)
  letI : ∀ U : C,
      Quiver.IsThin ((relativeInertiaProjection (FibredCategoryMor.toFunctor F) X.p).Fiber U) :=
    relativeInertiaProjection_fiber_isThin_of_source (F := F)
  -- The definition of fibred-in-setoids is exactly fibred-in-groupoids plus thin fibers.
  infer_instance

-- Proof sketch: the absolute self-inertia thinness proof is the same fiberwise argument as the
-- relative case, with the raw source projection used as both functors.
/-- Helper for Chap08 Lemma 8 7 1: absolute-inertia fibers are thin when the source fibers are
thin. -/
private theorem relativeInertiaProjectionSelf_fiber_isThin_of_source
    (X : FibredCategoryOver C) [IsFibredInSetoids X.p] (U : C) :
    Quiver.IsThin ((relativeInertiaProjection X.p X.p).Fiber U) := by
  intro A B
  refine ⟨?_⟩
  intro φ ψ
  -- Forget both inertia morphisms to the thin source fiber over `U`.
  apply Functor.Fiber.hom_ext
  apply RelativeInertiaHom.ext
  let q := relativeInertiaProjection X.p X.p
  letI : q.IsHomLift (𝟙 U) φ.1 := φ.2
  letI : q.IsHomLift (𝟙 U) ψ.1 := ψ.2
  letI : X.p.IsHomLift (𝟙 U) φ.1.φ := by
    refine of_fac' X.p (𝟙 U) φ.1.φ ?_ ?_ ?_
    · simpa [q, relativeInertiaProjection] using domain_eq q (𝟙 U) φ.1
    · simpa [q, relativeInertiaProjection] using codomain_eq q (𝟙 U) φ.1
    · simpa [q, relativeInertiaProjection] using fac' q (𝟙 U) φ.1
  letI : X.p.IsHomLift (𝟙 U) ψ.1.φ := by
    refine of_fac' X.p (𝟙 U) ψ.1.φ ?_ ?_ ?_
    · simpa [q, relativeInertiaProjection] using domain_eq q (𝟙 U) ψ.1
    · simpa [q, relativeInertiaProjection] using codomain_eq q (𝟙 U) ψ.1
    · simpa [q, relativeInertiaProjection] using fac' q (𝟙 U) ψ.1
  have h :
      homMk X.p U φ.1.φ = homMk X.p U ψ.1.φ := by
    exact Subsingleton.elim _ _
  exact congrArg (fun η => η.1) h

/-- Helper for Chap08 Lemma 8 7 1: the absolute-inertia projection is fibred in setoids when
the source projection is. -/
private theorem relativeInertiaProjectionSelf_isFibredInSetoids_of_source
    (X : FibredCategoryOver C) [IsFibredInSetoids X.p] :
    IsFibredInSetoids (relativeInertiaProjection X.p X.p) := by
  letI : IsFibredInGroupoids (relativeInertiaProjection X.p X.p) :=
    relativeInertiaProjectionSelf_isFibredInGroupoids_of_source X
  letI : ∀ U : C, Quiver.IsThin ((relativeInertiaProjection X.p X.p).Fiber U) :=
    relativeInertiaProjectionSelf_fiber_isThin_of_source X
  -- The definition of fibred-in-setoids is exactly fibred-in-groupoids plus thin fibers.
  infer_instance

/- Domain-style sampling for Lemma 8.7.1:
- primary domain: relative and absolute inertia of morphisms of stacks over a site.
- inspected owner-level declarations:
  `FibredCategoryOver.relativeInertiaOver`,
  `FibredCategoryOver.absoluteInertiaOver`,
  `StackOver`,
  `StackInGroupoidsOver`,
  `StackInSetoidsOver`.
- best owner abstraction: Chapter 4 already owns the inertia objects as fibred categories over the
  base, so this file should state only the Chapter 8 closure results saying that those owner
  objects are again stacks, stacks in groupoids, and stacks in setoids.
- primitive data: a morphism of fibred categories over `C` whose source and target satisfy the
  relevant stack, stack-in-groupoids, or stack-in-setoids owner predicates.
- derived API: the stack-closure theorems and the rebundled `StackOver` views
  `relativeInertiaStack` and `absoluteInertiaStack`.

Source/core/bridge triage:
- `source-facing`: the closure statements in Lemma 8.7.1.
- `core/canonical`: `FibredCategoryOver.relativeInertiaOver` and
  `FibredCategoryOver.absoluteInertiaOver`.
- `bridge/view`: the bundled `StackOver` abbreviations below. -/

-- Proof sketch: identify the relative inertia with the explicit iterated `2`-fibre product from
-- Lemma `4.34.1`, apply Lemma `8.4.6` to that explicit model, and specialize the same argument to
-- the absolute inertia.
/-- Chap08 Lemma 8 7 1 (1): the relative inertia of a morphism of stacks over `(C, J)` and the absolute
inertia of its source are again stacks over `(C, J)`. -/
@[stacks 036Y]
theorem relative_and_absolute_inertia_are_stacks
    {X Y : FibredCategoryOver C} [IsStackOnSite J X.p] [IsStackOnSite J Y.p] (F : X ⟶ Y) :
    IsStackOnSite J
        (FibredCategoryOver.relativeInertiaOver F).p ∧
      IsStackOnSite J
        (FibredCategoryOver.absoluteInertiaOver X).p := by
  constructor
  · -- The relative statement is the stack-transport helper along the inertia/pullback equivalence.
    exact relativeInertiaOver_isStackOnSite (J := J) F
  · -- The absolute statement is isolated in the raw self-inertia stack helper.
    exact absoluteInertiaOver_isStackOnSite_aux (J := J) X

-- Proof sketch: use the same relative-inertia/iterated-`2`-fibre-product identification from
-- Lemma `4.34.1`, then invoke Lemma `8.5.6` for the explicit `2`-fibre product and specialize to
-- the absolute inertia of the source stack.
/-- Lemma 8.7.1 (2): if the source and target are stacks in groupoids over `(C, J)`, then the
relative inertia and the absolute inertia of the source are also stacks in groupoids over
`(C, J)`. -/
@[stacks 036Y]
theorem relative_and_absolute_inertia_are_stacks_in_groupoids
    {X Y : FibredCategoryOver C}
    [IsStackInGroupoids J X.p] [IsStackInGroupoids J Y.p] (F : X ⟶ Y) :
    IsStackInGroupoids J
        (FibredCategoryOver.relativeInertiaOver F).p ∧
      IsStackInGroupoids J
        (FibredCategoryOver.absoluteInertiaOver X).p := by
  constructor
  · -- Combine the stack part with the source-fiber groupoid inheritance proved above.
    letI : IsStackOnSite J (FibredCategoryOver.relativeInertiaOver F).p :=
      (relative_and_absolute_inertia_are_stacks (J := J) F).1
    letI : IsFibredInGroupoids (FibredCategoryOver.relativeInertiaOver F).p := by
      simpa [FibredCategoryOver.relativeInertiaOver] using
        relativeInertiaProjection_isFibredInGroupoids_of_source (F := F)
    infer_instance
  · -- Absolute inertia uses the existing absolute groupoid inheritance for raw self-inertia.
    letI : IsStackOnSite J (FibredCategoryOver.absoluteInertiaOver X).p :=
      (relative_and_absolute_inertia_are_stacks (J := J) F).2
    letI : IsFibredInGroupoids (FibredCategoryOver.absoluteInertiaOver X).p := by
      simpa [FibredCategoryOver.absoluteInertiaOver, FibredCategoryOver.relativeInertiaOver] using
        relativeInertiaProjectionSelf_isFibredInGroupoids_of_source X
    infer_instance

/-- The relative inertia of a morphism of stacks over `(C, J)`, viewed again as a stack over
`(C, J)`. -/
abbrev relativeInertiaStack
    {X Y : FibredCategoryOver C} [IsStackOnSite J X.p] [IsStackOnSite J Y.p] (F : X ⟶ Y) :
    StackOver J :=
  ⟨
    FibredCategoryOver.relativeInertiaOver F,
    (relative_and_absolute_inertia_are_stacks F).1
  ⟩

/-- The absolute inertia of a stack over `(C, J)` is again a stack over `(C, J)`. -/
instance absoluteInertiaOver_isStackOnSite
    (X : FibredCategoryOver C) [IsStackOnSite J X.p] :
    IsStackOnSite J (FibredCategoryOver.absoluteInertiaOver X).p := by
  -- Reuse the isolated absolute stack helper so the bundled view below can infer the instance.
  exact absoluteInertiaOver_isStackOnSite_aux (J := J) X

/-- The absolute inertia of a stack over `(C, J)`, viewed again as a stack over `(C, J)`. -/
abbrev absoluteInertiaStack (X : FibredCategoryOver C) [IsStackOnSite J X.p] :
    StackOver J :=
  ⟨
    FibredCategoryOver.absoluteInertiaOver X,
    inferInstance
  ⟩

-- Proof sketch: combine Lemma `4.34.1` with Lemma `8.6.6` for the explicit iterated
-- `2`-fibre-product model of relative inertia to obtain the setoid-fiber condition, while the
-- stack condition itself comes from the stack case above.
/-- Lemma 8.7.1 (3): if the source and target are stacks in setoids over `(C, J)`, then the
relative inertia of the morphism and the absolute inertia of the source are again stacks in
setoids over `(C, J)`. -/
@[stacks 036Y]
theorem relative_and_absolute_inertia_are_stacks_in_setoids
    {X Y : FibredCategoryOver C}
    [IsStackInSetoids J X.p] [IsStackInSetoids J Y.p] (F : X ⟶ Y) :
    IsStackInSetoids J
        (FibredCategoryOver.relativeInertiaOver F).p ∧
      IsStackInSetoids J
        (FibredCategoryOver.absoluteInertiaOver X).p := by
  constructor
  · -- Thin source fibers pass to relative-inertia fibers, and the stack part comes from (1).
    letI : IsStackOnSite J (FibredCategoryOver.relativeInertiaOver F).p :=
      (relative_and_absolute_inertia_are_stacks (J := J) F).1
    letI : IsFibredInSetoids (FibredCategoryOver.relativeInertiaOver F).p := by
      simpa [FibredCategoryOver.relativeInertiaOver] using
        relativeInertiaProjection_isFibredInSetoids_of_source (F := F)
    infer_instance
  · -- Specialize the same source-fiber setoid inheritance to raw self-inertia.
    letI : IsStackOnSite J (FibredCategoryOver.absoluteInertiaOver X).p :=
      (relative_and_absolute_inertia_are_stacks (J := J) F).2
    letI : IsFibredInSetoids (FibredCategoryOver.absoluteInertiaOver X).p := by
      simpa [FibredCategoryOver.absoluteInertiaOver] using
        relativeInertiaProjectionSelf_isFibredInSetoids_of_source X
    infer_instance

/-- The absolute inertia of a stack in setoids is again a stack in setoids. -/
instance absoluteInertiaOver_isStackInSetoids
    (X : FibredCategoryOver C) [IsStackInSetoids J X.p] :
    IsStackInSetoids J (FibredCategoryOver.absoluteInertiaOver X).p := by
  -- Assemble the absolute stack and setoid-fiber parts directly, avoiding an unnecessary
  -- identity morphism in the ambient bicategorical owner.
  letI : IsStackOnSite J (FibredCategoryOver.absoluteInertiaOver X).p :=
    absoluteInertiaOver_isStackOnSite_aux (J := J) X
  letI : IsFibredInSetoids (FibredCategoryOver.absoluteInertiaOver X).p := by
    simpa [FibredCategoryOver.absoluteInertiaOver] using
      relativeInertiaProjectionSelf_isFibredInSetoids_of_source X
  infer_instance

end

end CategoryTheory
